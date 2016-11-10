package dotty.tools.dotc
package transform.linker

import core._
import Contexts.Context
import Flags._
import Symbols._
import SymDenotations._
import Types._
import Decorators._
import DenotTransformers._
import StdNames._
import NameOps._
import ast.Trees._
import dotty.tools.dotc.ast.tpd
import util.Positions._
import Names._
import dotty.tools.dotc.core.Constants.Constant
import dotty.tools.dotc.transform.TreeTransforms
import dotty.tools.dotc.transform.TreeTransforms.{MiniPhaseTransform, TransformerInfo, TreeTransform}

import collection.mutable
import scala.collection.immutable.::


/** This phase applies rewritings provided by libraries. */
class Rewrites extends MiniPhaseTransform { thisTransform =>
  import ast.tpd._

  override def phaseName: String = "rewrites"
  val namePattern = "$opt"

  def isOptVersion(n: Name) = n.endsWith(namePattern)
  def dropOpt(n: Name)(implicit ctx: Context) = if (isOptVersion(n)) n.dropRight(namePattern.length) else n

  private var annot             : Symbol = null
  private var rewriteClass      : Symbol = null
  private var warningClass      : Symbol = null
  private var errorClass        : Symbol = null
  private var rewriteCompanion  : Symbol = null
  private var rewriteApply      : Symbol = null
  private var sourceArgument    : Symbol = null
  private var isPureArgument    : Symbol = null
  private var isLiteralArgument : Symbol = null
  private var supportedArguments: Set[Symbol] = null
  private var pairs             : List[(DefDef, DefDef)] = null


  def collectPatters(tree: tpd.Tree)(implicit ctx: Context) = {
    val collector = new TreeAccumulator[List[(DefDef, DefDef)]] {
      def apply(x: List[(tpd.DefDef, tpd.DefDef)], tree: tpd.Tree)(implicit ctx: Context): List[(tpd.DefDef, tpd.DefDef)] = {
        tree match {
          case t: tpd.TypeDef if t.isClassDef && t.symbol.hasAnnotation(annot) =>
            val stats = t.rhs.asInstanceOf[Template].body
            val prepend = stats.flatMap{x => x match {
              case defdef: DefDef if defdef.symbol.info.finalResultType.derivesFrom(rewriteClass) || defdef.symbol.info.finalResultType.derivesFrom(warningClass)=>
                seb(defdef.rhs) match {
                  case t: Apply if t.symbol eq rewriteApply =>
                    (cpy.DefDef(defdef)(rhs = t.args.head), cpy.DefDef(defdef)(rhs = t.args.tail.head)) :: Nil
                  case t: Apply if t.tpe.derivesFrom(warningClass) =>
                    ctx.error("warning are not implemented yet", t.pos)
                    Nil
                  case _ =>
                    ctx.error("tree not supported", defdef.pos)
                    Nil
                }
              case _ => Nil
            }}
            foldOver(prepend ::: x, t)
          case _ => foldOver(x, tree)
        }
      }
    }
    collector.apply(Nil, tree)
  }

  override def prepareForUnit(tree: tpd.Tree)(implicit ctx: Context): TreeTransform = {
    if (!ctx.settings.rewrites.value) return TreeTransforms.NoTransform
    annot = ctx.requiredClass("dotty.linker.rewrites")
    rewriteClass = ctx.requiredClass("dotty.linker.Rewrite")
    warningClass = ctx.requiredClass("dotty.linker.Warning")
    errorClass = ctx.requiredClass("dotty.linker.Error")

    isPureArgument = ctx.requiredClass("dotty.linker.IsPure")
    sourceArgument = ctx.requiredClass("dotty.linker.Source")
    isLiteralArgument = ctx.requiredClass("dotty.linker.IsLiteral")

    supportedArguments = Set(isLiteralArgument, sourceArgument, isPureArgument)
    rewriteCompanion = rewriteClass.companionModule
    rewriteApply = rewriteCompanion.requiredMethod(nme.apply)
    pairs = collectPatters(tree)
    ctx.warning(s"found rewriting rules: ${pairs.map(x=> x._1.symbol.showFullName).mkString(", ")}")
    pairs.foreach(checkSupported)
    this
  }

  private def checkSupported(pair :(tpd.DefDef, tpd.DefDef))(implicit ctx: Context): Unit = {
    val pattern = pair._1
    val rewrite = pair._2
    def unsupported(reason: String) = ctx.error("Unsupported pattern: " + reason, pattern.pos)
    pattern.symbol.info.resultType match {
      case t: ImplicitMethodType =>
        val ptypes = t.paramTypes
        def checkValidCondition(t: Type) = t match{
          case t: RefinedType if supportedArguments.contains(t.typeSymbol) =>
            val info = t.refinedInfo
            info match {
              case alias: TypeAlias =>
                alias.underlying match {
                  case t: MethodParam =>
                  case _ =>
                    ctx.error(i"Unsupported condition $t", pattern.pos)
                }
            }
          case _ =>
            ctx.error(i"Unsupported condition $t", pattern.pos)
        }
        ptypes.foreach(checkValidCondition)
      case t: MethodType =>
        ctx.error("multiple argument strings not supported", pattern.pos)
      case _ =>
    }
    new TreeTraverser {
      def traverse(tree: tpd.Tree)(implicit ctx: Context): Unit =
        tree match {
          case t: Apply => traverseChildren(tree)
          case Block(Nil, exp) => traverse(exp)
          case t @ Block(List(fn: DefDef), c: Closure) =>
            unsupported(s"No closures in patterns yet. Sorry. Use function-arguments instead.")
          //traverseChildren(fn.rhs)
          case t: Literal => ()
          case _: Select | _: Ident => traverseChildren(tree)
          case _ => unsupported(s"${tree.getClass.getSimpleName} tree is currently unsupported")
        }
    }.traverse(pattern.rhs)
  }


  override def transformUnit(tree: tpd.Tree)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    annot = null
    pairs = null
    tree
  }


  override def prepareForTypeDef(tree: tpd.TypeDef)(implicit ctx: Context): TreeTransform = {
    if (tree.symbol.hasAnnotation(annot)) TreeTransforms.NoTransform
    else this
  }

  type Substitution = Map[Name, (Tree, Symbol /* owner */)]

  private def filtersByPattern(filters: List[ValDef])(implicit ctx: Context): Substitution => Option[Substitution] = {
    if (filters.isEmpty) {x: Substitution => Some(x)}
    else {
      val headFilter = filters.head.symbol.info.typeSymbol
      val methodParamName = filters.head.symbol.info.asInstanceOf[RefinedType].
        refinedInfo.asInstanceOf[TypeAlias].underlying.asInstanceOf[TermRef].name
      if (headFilter eq isLiteralArgument) { x: Substitution =>
         x.get(methodParamName) match {
           case Some((t: Literal, _)) =>
             filtersByPattern(filters.tail)(ctx)(x)
           case _ =>
             None
         }
      } else if (headFilter eq sourceArgument) { x: Substitution =>
        val sourceText = Literal(Constant(x(methodParamName)._1.show))
        val newSubstitution : Substitution = x + (filters.head.name -> (sourceText, NoSymbol))
        filtersByPattern(filters.tail)(ctx)(newSubstitution)
      } else if (headFilter eq isPureArgument) {x: Substitution =>
        if (isPureTree(x(methodParamName)._1)) filtersByPattern(filters.tail)(ctx)(x)
        else None
      } else ???
    }
  }

  private def isPureTree(t: Tree)(implicit ctx: Context) = {
    tpd.isPureExpr(t)
  }

  override def transformDefDef(tree: tpd.DefDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    if (tree.symbol.ownersIterator.findSymbol(x => x.hasAnnotation(annot)).exists) tree
    else {
      val mapping = new TreeMap() {
        override def transform(tree: tpd.Tree)(implicit ctx: Context):tpd.Tree = tree match {
          case tree: DefTree =>
            super.transform(tree)(ctx.withOwner(tree.symbol))
          case _ =>
            val scanner = pairs.iterator.map(x => (x, isSimilar(tree, x._1))).find(x => x._2.nonEmpty)
            if (scanner.nonEmpty) {
              val ((patern, rewrite), Some(binding)) = scanner.get
              val fistSubstitution: Substitution = binding.map(x => (x._1.name, x._2)).toMap
              val filters =
                if (patern.symbol.info.resultType.isInstanceOf[ImplicitMethodType])
                  patern.vparamss.tail.head
                else Nil
              val secondSubstitution = filtersByPattern(filters)(ctx)(fistSubstitution)

              if (secondSubstitution.nonEmpty) {
                val finalSubstitution = secondSubstitution.get
                ctx.warning(s"Applying rule ${dropOpt(rewrite.symbol.name)}, substitution: ${finalSubstitution.map(x => s"${x._1} -> ${x._2._1.show}").mkString(", ")}")
                val substitution = new TreeMap() {
                  override def transform(tree: tpd.Tree)(implicit ctx: Context): tpd.Tree = tree match {
                    case tree: DefTree =>
                      super.transform(tree)(ctx.withOwner(tree.symbol))
                    case _ =>
                      if (tree.symbol.maybeOwner == rewrite.symbol && tree.symbol.is(Flags.Param)) {
                        val (oldTree, oldOwner) = finalSubstitution(tree.symbol.name)
                        if (oldOwner.exists) oldTree.changeOwner(oldOwner, ctx.owner)
                        else oldTree
                      }
                      else super.transform(tree)
                  }
                }
                super.transform(substitution.transform(rewrite.rhs)).changeOwner(rewrite.symbol, ctx.owner)
              } else super.transform(tree)
            } else super.transform(tree)
        }
      }

      mapping.transform(tree)
    }
  }

  override def transformTypeDef(tree: tpd.TypeDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    if (tree.symbol.hasAnnotation(annot) && !(tree.symbol.isStatic && tree.symbol.is(Flags.Module)))
      ctx.error("Rewrite rulles can only be defined in top level module classes", tree.pos)

    tree
  }


  private def isSimilar(tree: Tree, pattern: DefDef)(implicit ctx: Context): Option[Map[Symbol, (Tree, Symbol)]] = {
    val currentMapping = new mutable.HashMap[Symbol, (Tree, Symbol)]()
    var aborted = false
    def abort = aborted = true
      def bind(sym: Symbol, tree: Tree, oldOwner: Symbol) = {
        if (currentMapping.contains(sym)) abort
        else currentMapping.put(sym, (tree, oldOwner))
      }
      def loop(subtree: Tree, subpat: Tree)(implicit ctx: Context): Unit = if (!aborted) seb(subtree) match {
        case Apply(sel, args) => seb(subpat) match {
          case Apply(selpat, selargs) if selargs.hasSameLengthAs(args) =>
            loop(sel, selpat)
            args.zip(selargs).foreach(x => loop(x._1, x._2))
          case subpat: Ident if (subpat.symbol.owner == pattern.symbol && subpat.symbol.is(Flags.Param)) => // new binding
            bind(subpat.symbol, subtree, ctx.owner)
          case _ =>
            abort
        }
        case TypeApply(fn, targs) => seb(subpat) match {
          case TypeApply(selfn, seltargs) =>
            loop(fn, selfn)
            targs.zip(seltargs).foreach(x => x._1.tpe =:= x._2.tpe)
          case _ => abort
        }
        case Block(List(fn: DefDef), c: Closure) => seb(subpat) match {
          case subpat: Ident if (subpat.symbol.owner == pattern.symbol && subpat.symbol.is(Flags.Param)) => // new binding
            bind(subpat.symbol, subtree, ctx.owner)
          case _ => abort
        }
        case subtree: Ident => seb(subpat) match {
          case subpat: Ident if (subpat.symbol.owner == pattern.symbol && subpat.symbol.is(Flags.Param)) => // new binding
            bind(subpat.symbol, subtree, ctx.owner)
          case subpat: RefTree if (subpat.symbol eq subtree.symbol) => //same ref
          case _ => abort
        }
        case subtree: Select => seb(subpat) match {
          case subpat: Ident if (subpat.symbol.owner == pattern.symbol && subpat.symbol.is(Flags.Param)) => // new binding
            bind(subpat.symbol, subtree, ctx.owner)
          case subpat: Select if (subpat.symbol eq subtree.symbol) => //same ref
            loop(subtree.qualifier, subpat.qualifier)
          case _ => abort
        }
        case subtree: Literal => seb(subpat) match {
          case subpat: Ident if (subpat.symbol.owner == pattern.symbol && subpat.symbol.is(Flags.Param)) => // new binding
            bind(subpat.symbol, subtree, ctx.owner)
          case subpat: Literal if (subpat.const.value == subtree.const.value) =>   //todo: is it fine to ignore tag?
          case _ => abort
        }
        case _ => abort
      }
      loop(tree, pattern.rhs)

    if (aborted || currentMapping.size != pattern.vparamss.head.size) None
    else Some(currentMapping.toMap)
  }

  private def seb/*skipEmptyBlocks*/(x: Tree) = x match {
    case Block(Nil, t) => t
    case _ => x
  }
}
