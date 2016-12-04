package dotty.tools.dotc
package transform

import TreeTransforms._
import core._
import Symbols._
import Contexts._
import Types._
import Flags._
import ast.Trees._
import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.transform.IdempotentTree.IdempotentTree

import scala.annotation.tailrec

/** This phase performs Common Subexpression Elimination (CSE) that
  * precomputes an expression into a new variable when it's used
  * several times within the same scope.
  *
  * This optimization is applied for either vals, lazy vals or
  * expressions annotated with `Idempotent`. Such annotation is used to
  * ensure to the compiler that a concrete expression has no side effects.
  *
  * For instance, the following code:
  * {{{
  *   val a = 1
  *   val b = a + a + 2
  *   val c = a + a + 4
  * }}}
  *
  * will be transformed to:
  * {{{
  *   val a = 1
  *   val a1 = a + a
  *   val b = a1 + 2
  *   val c = a1 + 2
  * }}}
  *
  * only if `+` is guaranteed to be immutable.
  *
  * Originally written by @allanrenucci, redesigned and improved by @jvican.
  *
  */
class ElimCommonSubexpression extends MiniPhaseTransform {

  import ast._
  import ast.tpd._
  import Decorators._

  override def phaseName = "elimCommonSubexpression"

  override def runsAfter = Set(classOf[ElimByName])

  /* Imitate `Simplify` structure for the moment being */
  type Visitor = Tree => Unit
  val NoVisitor: Visitor = (_) => ()
  type Transformer = () => (Tree => Tree)
  type Optimization = (Context) => (String, Visitor, Transformer)

  /** Performs CSE only **once** and does not repeat the transformation.
    * If you add a `while` check that the transformation is first idempotent,
    * in the true meaning of the word. Otherwise, infinite cycles may happen. */
  override def transformDefDef(tree: tpd.DefDef)(
      implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    if (!tree.symbol.is(Flags.Label)) {
      var rhs0 = tree.rhs
      val (name, nextVisitor, nextTransformer) = elimCommonSubexpression(
          ctx.withOwner(tree.symbol))
      rhs0.foreachSubTree(nextVisitor)
      val transformer = nextTransformer()
      val rhst = new TreeMap() {
        override def transform(
            tree: tpd.Tree)(implicit ctx: Context): tpd.Tree =
          transformer(super.transform(tree))
      }.transform(rhs0)
      if (rhst ne rhs0)
        println(s"${tree.symbol} after $name became ${rhst.show}")
      rhs0 = rhst
      if (rhs0 ne tree.rhs) cpy.DefDef(tree)(rhs = rhs0)
      else tree
    } else tree
  }

  /** Lifted up val def and tree referencing to it */
  type Optimized = (ValDef, Tree)

  def elimCommonSubexpression: Optimization = (ctx0: Context) => {
    implicit val ctx = ctx0

    import collection.mutable

    /* Trees whose inner trees are candidates for CSE */
    val hostsOfOptimizations = mutable.HashSet[Symbol]()

    /* Map symbols of ValDef or DefDef to their **original** rhs */
    val originalRhs = mutable.HashMap[Symbol, Tree]()

    /* Map childs to parents. A child is a subtree of an idempotent tree. */
    val parents = mutable.HashMap[IdempotentTree, IdempotentTree]()

    /* Trees that have already been analyzed by the visitor */
    val analyzed = mutable.HashSet[Tree]()

    // TODO: This could be removed in the future, but it's quite handy now
    /* Idempotent trees are expensive to build, cache to reuse them*/
    val cached = mutable.HashMap[Tree, List[IdempotentTree]]()

    /* Keep track of the number of appearances of every idempotent tree. */
    var appearances = mutable.HashMap[IdempotentTree, Int]()

    /* Store necessary information to optimize these idempotent trees. */
    val optimized = mutable.HashMap[IdempotentTree, Optimized]()

    /* Map normal trees to the unique idempotent instance that represents them. */
    val candidatesOptimized = mutable.HashMap[Tree, IdempotentTree]()

    /* Keep track of the valdefs that have already been introduced by the transformer. */
    val processedValDefs = mutable.HashSet[ValDef]()

    /* Map an idempotent tree to all the trees that have the same representation. */
    val transfomerTargets = mutable.HashMap[IdempotentTree, mutable.Set[Tree]]()

    @scala.annotation.tailrec
    def linkChildsToParents(trees: List[IdempotentTree]): Unit = {
      trees match {
        case child :: parent :: tail =>
          parents += (child -> parent)
          linkChildsToParents(tail)
        case _ =>
      }
    }

    val emptyMutableSet = collection.mutable.HashSet[Tree]()

    val analyzer: Visitor = {
      case Ident(_) | EmptyTree | This(_) | Super(_, _) | Literal(_) =>
      // This avoids visiting unnecessary Idempotent instances

      case vdef: ValOrDefDef if !analyzed.contains(vdef) =>
        originalRhs += (vdef.symbol -> vdef.rhs)

      case tree: Tree if !analyzed.contains(tree) =>
        //println(s"Analyzing $tree")
        IdempotentTree.from(tree) match {
          case Some(idempotent) =>
            val allSubTrees = IdempotentTree.allIdempotentTrees(idempotent)
            cached += idempotent.tree -> allSubTrees
            linkChildsToParents(allSubTrees.reverse)
            allSubTrees.foreach { st =>
              val tree = st.tree
              analyzed += tree
              val current = appearances.getOrElse(st, 0)
              appearances += st -> (current + 1)
              val targets = transfomerTargets.getOrElse(st, emptyMutableSet)
              transfomerTargets += (st -> (targets += st.tree))
            }

          case _ =>
        }

      case _ =>
    }

    val visitor: Visitor = {
      case b: Block if !analyzed.contains(b) =>
        analyzed += b
        // Optimizing within blocks for the moment
        b.foreachSubTree(analyzer)

      case vdef: ValOrDefDef if analyzed.contains(vdef.rhs) =>
        if (cached.contains(vdef.rhs))
          hostsOfOptimizations += vdef.symbol

      case t =>
    }

    val transformer: Transformer = () => {
      val optimizationTargets = appearances.filter(_._2 > 1)
      val candidates = optimizationTargets.toList.sortBy(_._2)

      def getHighestParent(idem: IdempotentTree): Option[IdempotentTree] = {
        @tailrec
        def loop(idem: IdempotentTree,
                 acc: Option[IdempotentTree]): Option[IdempotentTree] = {
          parents.get(idem) match {
            case hit @ Some(parent) => loop(parent, hit)
            case None => acc
          }
        }
        loop(idem, None)
      }

      @tailrec
      def getParentOptimization(idem: IdempotentTree): Option[Optimized] = {
        parents.get(idem) match {
          case hit @ Some(parent) =>
            val opt = optimized.get(idem)
            if (opt.isDefined) opt
            else getParentOptimization(parent)
          case None => None
        }
      }

      candidates.foreach { cand =>
        val (idem, count) = cand
        if (!optimized.contains(idem)) {

          /* This part is quite inefficient and could be solved by
           * introducing a notion of order when optimizing the candidates,
           * in order to avoid checking if parents of an idempotent tree
           * have already been optimized, and if so reuse their references. */
          val optimizedTree = getParentOptimization(idem) match {
            case Some(tp) =>
              val (parentValDef, parentRef) = tp
              // Reuse the transformation of the parent and replace it in the tree
              IdempotentTree.replace(parentValDef.rhs, idem.tree, parentRef)

            case None =>
              getHighestParent(idem) flatMap appearances.get match {
                case Some(parentCount) if parentCount >= count => EmptyTree
                case _ => idem.tree
              }
          }

          if (optimizedTree != EmptyTree) {
            val termName = ctx.freshName("cse").toTermName
            val vdef = tpd.SyntheticValDef(termName, optimizedTree)
            val ref = tpd.ref(vdef.symbol)
            optimized += (idem -> (vdef -> ref))

            // Subscribe transformer targets
            transfomerTargets.get(idem) match {
              case Some(allTargets) =>
                allTargets foreach { t =>
                  candidatesOptimized += (t -> idem)
                }
              case None =>
            }
          }
        }
      }

      appearances = null // Free up unnecessary memory

      val transformation: Tree => Tree = {
        case enclosingTree: ValOrDefDef
            if hostsOfOptimizations.contains(enclosingTree.symbol) =>
          hostsOfOptimizations -= enclosingTree.symbol

          // Get the original rhs, `vdef.rhs` has changed
          val associatedRhs = originalRhs(enclosingTree.symbol)
          val topLevelIdempotent = cached(associatedRhs).iterator
          val optimizedIdempotents =
            topLevelIdempotent.map(optimized.get).filter(_.isDefined)
          val newValDefs = optimizedIdempotents
            .map(_.get._1)
            .filterNot(processedValDefs.contains)
            .toList
          newValDefs.foreach(vd => processedValDefs += vd)
          tpd.Thicket(newValDefs ::: List(enclosingTree))

        case tree =>
          candidatesOptimized.get(tree) match {
            case Some(idem) =>
              optimized.get(idem) match {
                case Some((vdef, ref)) => ref
                case None => tree
              }
            case None => tree
          }
      }
      transformation
    }

    ("elimCommonSubexpression", visitor, transformer)
  }
}

object IdempotentTree {

  import ast.tpd._

  class IdempotentTree(val tree: tpd.Tree)(implicit ctx: Context) {

    import scala.util.hashing.MurmurHash3.{seqHash, mix}

    /** Witness of structural equality by inspecting the tree */
    def idempotentHashCode(t: Tree)(implicit ctx: Context): Int = {
      t match {
        case EmptyTree => EmptyTree.hashCode()
        case _: This => t.symbol.hashCode()
        case _: Super => t.symbol.hashCode()
        case _: Ident => t.symbol.hashCode()
        case Literal(constant) => constant.value.hashCode()
        case Select(qual, name) =>
          mix(name.hashCode(), idempotentHashCode(qual))
        case Apply(fun1, args1) =>
          val idempotents = seqHash(args1.map(idempotentHashCode))
          mix(idempotentHashCode(fun1), idempotents)
        case TypeApply(fun1, targs1) =>
          val idempotents = seqHash(targs1.map(idempotentHashCode))
          mix(idempotentHashCode(fun1), idempotents)
        // TODO: Case for `Typed`
        case _ => 0 // impossible case
      }
    }

    override def hashCode(): Int = idempotentHashCode(this.tree)

    /** Compare idempotent trees by structural equality */
    override def equals(that: Any): Boolean = that match {
      case thatIdempotent: IdempotentTree =>
        this.hashCode() == thatIdempotent.hashCode()
      case _ => false
    }
  }

  import ast._
  import ast.tpd._

  // Never call directly without having checked that it's indeed idempotent
  private def apply(tree: Tree)(implicit ctx: Context): IdempotentTree =
    new IdempotentTree(tree)

  def from(tree: Tree)(implicit ctx: Context): Option[IdempotentTree] =
    if (isIdempotent(tree)) Some(new IdempotentTree(tree)) else None

  def isIdempotent(tree: Tree)(implicit ctx: Context): Boolean = {

    /** Expressions known to be initialized once are idempotent (lazy vals
      * and vals), as well as methods annotated with `Idempotent` */
    def isIdempotentRef(tree: Tree): Boolean = {
      val sym = tree.symbol
      if (sym hasAnnotation defn.IdempotentAnnot) true // @Idempotent
      else if (sym is Lazy) true // lazy val and singleton objects
      else !(sym is Mutable) && !(sym is Method) // val
    }

    tree match {
      case EmptyTree | This(_) | Super(_, _) | Literal(_) => true
      case Ident(_) => isIdempotentRef(tree)
      case Select(qual, _) => isIdempotent(qual) && isIdempotentRef(tree)
      case TypeApply(fn, _) => isIdempotent(fn)
      case Apply(fn, args) => isIdempotent(fn) && (args forall isIdempotent)
      case Typed(expr, _) => isIdempotent(expr)
      case _ => false
    }
  }

  /** Collects all the idempotent sub trees, including the original tree. */
  def allIdempotentTrees(t1: IdempotentTree)(
      implicit ctx: Context): List[IdempotentTree] = {
    // TODO: Pending to remove Typed casts to remove comparison failures
    def collect(isTopTree: Boolean, tree: Tree): List[IdempotentTree] =
      tree match {
        case EmptyTree | This(_) | Super(_, _) | Literal(_) | Ident(_) => Nil
        case Select(qual, _) =>
          if (isTopTree)
            IdempotentTree(tree) :: collect(isTopTree = false, qual)
          else collect(isTopTree, qual)
        case TypeApply(fn, _) =>
          if (isTopTree) IdempotentTree(tree) :: collect(isTopTree = false, fn)
          else collect(isTopTree, fn)
        case Apply(fn, args) =>
          val branched = args.map(collect(true, _)).reduce(_ ++ _)
          if (isTopTree)
            IdempotentTree(tree) :: collect(isTopTree = false, fn) ::: branched
          else collect(isTopTree, fn) ::: branched
        case Typed(expr, _) =>
          if (isTopTree)
            IdempotentTree(tree) :: collect(isTopTree = false, expr)
          else collect(isTopTree, expr)
        case _ => Nil // Impossible case, t1 is idempotent
      }

    collect(isTopTree = true, t1.tree)
  }

  /** Replace a targeted **idempotent** subtree by a reference to another new tree.
    * Only use this utility with trees that are known to be Idempotent. */
  def replace(tree: Tree, target: Tree, ref: Tree)(
      implicit ctx: Context): Tree = {
    tree match {
      case _: Tree if tree == target => ref
      case Select(qual, name) => Select(replace(qual, target, ref), name)
      case TypeApply(fn, targs) => TypeApply(replace(fn, target, ref), targs)
      case Apply(fn, args) =>
        val replacedArgs = args.map(replace(_, target, ref))
        Apply(replace(fn, target, ref), replacedArgs)
      case Typed(expr, tpe) => Typed(replace(expr, target, ref), tpe)
      case t => t
    }
  }
}
