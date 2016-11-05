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
import java.util

import Names._
import dotty.tools.dotc.core.Constants.Constant
import dotty.tools.dotc.core.Phases.Phase
import dotty.tools.dotc.transform.{Erasure, Splitter, TreeTransforms}
import dotty.tools.dotc.transform.TreeTransforms.{MiniPhaseTransform, TransformerInfo, TreeTransform}

import scala.collection.JavaConversions
import collection.mutable
import scala.collection.immutable.::

/** This phase applies rewritings provided by libraries. */
class IdempotencyInference
  extends MiniPhaseTransform
    with IdentityDenotTransformer {
  thisTransform =>

  def phaseName: String = "IdempotencyInference"

  import tpd._

  /** List of names of phases that should precede this phase */
  override def runsAfter: Set[Class[_ <: Phase]] = Set(classOf[Splitter])

  private val collectedCalls = mutable.Map[Symbol, mutable.Set[Symbol]]()
  private val inferredIdempotent = mutable.Set[Symbol]()

  private[dotty] def markAsIdempotent(sym: Symbol) = inferredIdempotent += sym

  // TODO: check overriding rules.

  override def transformDefDef(tree: tpd.DefDef)(
    implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    val calls = collection.mutable.Set[Symbol]()
    tree.rhs.foreachSubTree {
      case t: RefTree =>
        if (!t.symbol.isContainedIn(tree.symbol))
          calls += t.symbol
      case _ =>
    }
    if (tree.rhs.isEmpty || tree.symbol.isSetter) calls += defn.Object_notify
    collectedCalls.put(tree.symbol, calls)
    tree
  }


  override def runOn(units: List[CompilationUnit])(implicit ctx: Context): List[CompilationUnit] = {
    val rez = super.runOn(units)
    commit(ctx.withPhase(this))
    rez
  }

  def commit(implicit ctx: Context) = {
    var changed = true
    var sizeStats: List[Int] = Nil
    while (changed) {
      changed = false
      sizeStats = (inferredIdempotent.size - sizeStats.sum) :: sizeStats
      collectedCalls.foreach {
        case (defn, calls) =>
          if (!assumedIdempotent(defn) && !inferredIdempotent(defn)) {
            if (calls.nonEmpty && calls.forall(call => isIdempotentRef(call))) {
              if ((!defn.symbol.isConstructor) ||
                (defn.symbol.owner.isValueClass ||
                  defn.symbol.owner.is(Flags.Module))) {
                changed = true
                inferredIdempotent += defn
                println(s"Inferred ${defn.showFullName} idempotent")
              }
            }
          }
      }
      val allCalls  = collectedCalls.keys.filter(assumedIdempotent).toSet
      println(
        s" * * * * Marked as idempotent ${inferredIdempotent.size} out of ${collectedCalls.size} methods, " +
          s"rounds: ${sizeStats.reverse}, seedSize: ${allCalls.size}")
    }
  }

  /** Check that the symbol points to a method which doesn't need parameters.
   * Use this method in order to check that idempotent trees are valid. */
  @inline def invalidMethodRef(sym: Symbol)(implicit ctx: Context) = {
    ((sym is Method) || (sym is Label)) &&
      !sym.info.paramTypess.forall(_.isEmpty) ||
      sym.info.widenDealias.isInstanceOf[PolyType]
  }

  /** Expressions known to be initialized once are idempotent (lazy vals
   * and vals), as well as methods annotated with `Idempotent` */
  def isIdempotentRef(sym: Symbol)(implicit ctx: Context): Boolean = {
    if ((sym hasAnnotation defn.IdempotentAnnot) || inferredIdempotent(sym))
      true // @Idempotent
    else {
      val isIdempotent = assumedIdempotent(sym)
      if (isIdempotent) inferredIdempotent += sym
      isIdempotent
    }
  }

  private def assumedIdempotent(sym: Symbol)(implicit ctx: Context): Boolean = {
    if (sym is Lazy) true // lazy val and singleton objects
    else if (!(sym is Mutable) && !(sym is Method)) true // val
    else if (sym.maybeOwner.isPrimitiveValueClass) true
    else if (sym == defn.Object_ne || sym == defn.Object_eq) true
    else if (sym == defn.Any_getClass || sym == defn.Any_asInstanceOf ||
      sym == defn.Any_isInstanceOf || sym == defn.Any_!= || sym == defn.Any_== ||
      sym == defn.throwMethod || sym == defn.String_+ || sym == defn.String_valueOf_Object) true
    else if (Erasure.Boxing.isBox(sym) || Erasure.Boxing.isUnbox(sym)) true
    else if (sym.isPrimaryConstructor && (sym.owner.is(Flags.Module) || sym.owner.derivesFrom(defn.ThrowableClass))) true
    else sym.isGetter && !(sym is Mutable)
  }

  /** Detect whether a tree is a valid idempotent or not, the semantics
   * of the method are tightly coupled with `allIdempotentTrees` in CSE. */
  def isIdempotent(tree: Tree)(implicit ctx: Context): Boolean = {
    def isParameterlessMethod(sym: Symbol) =
      sym.is(Flags.Method) && sym.info.isParameterless

    def loop(tree: Tree,
             pendingArgsList: Int,
             isTopLevel: Boolean = false): Boolean = {
      tree match {
        case Ident(_) =>
          val sym = tree.symbol
          if (pendingArgsList == 0 &&
              (!isTopLevel || (isTopLevel && isParameterlessMethod(sym)))) {
            isIdempotentRef(sym)
          } else false

        case EmptyTree | Literal(_) | This(_) | Super(_, _)
          if !isTopLevel => if (pendingArgsList == 0) true else false

        case Select(qual, _) =>
          loop(qual, pendingArgsList) && isIdempotentRef(tree.symbol)

        case TypeApply(fn, _) =>
          if (pendingArgsList > 0) false
          else loop(fn, pendingArgsList)

        case Apply(fn, args) =>
          val currentArgsList = if (pendingArgsList == 0) {
            val methodType = fn.symbol.info
            methodType.paramNamess.length - 1
          } else pendingArgsList - 1
          loop(fn, currentArgsList) && (args forall (t => loop(t, 0)))

        case _ => false
      }
    }

    loop(tree, 0, isTopLevel = true)
  }
}
