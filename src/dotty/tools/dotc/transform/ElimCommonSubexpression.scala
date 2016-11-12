package dotty.tools.dotc
package transform

import TreeTransforms._
import core._
import Symbols._
import Contexts._
import ast.Trees._
import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.transform.IdempotentTrees.IdempotentTree
import dotty.tools.dotc.transform.linker.IdempotencyInference
import State._
import dotty.tools.dotc.core.Constants.Constant

/** This phase performs Partial Redundancy Elimination (PRE) that
  * precomputes an expression into a new variable when it's used
  * several times within the same scope. It performs optimizations
  * across different scopes (branches and inner functions), and it is
  * therefore more powerful than Common Subexpression Elimination (CSE).
  *
  * This optimization is applied for either vals, lazy vals or
  * expressions annotated with `Idempotent`. Such annotation is used to
  * ensure to the compiler that a concrete expression has no side effects.
  *
  * @author jvican
  */
class ElimCommonSubexpression extends MiniPhaseTransform {

  import ast._
  import ast.tpd._
  import Decorators._

  override def phaseName = "elimCommonSubexpression"

  private final val debug = false
  private var optimizedTimes = 0

  override def runsAfter =
    Set(classOf[ElimByName], classOf[IdempotencyInference])

  type Analyzer = (Tree, Tree, Tree, Set[Symbol], OContext, Boolean, Boolean) => OContext
  type PreOptimizer = () => Unit
  type Transformer = (Tree => Tree)
  type Optimization = (Context) => (Analyzer, PreOptimizer, Transformer)

  import collection.mutable.ListBuffer

  type Traversal = ListBuffer[List[IdempotentTree]]
  type OContext = (State, (Traversal, Traversal))

  /** Represents the new declaration, assignation and reference. */
  type Optimized = (ValDef, Tree)

  def reportError(msg: String, tree: Tree)(implicit ctx: Context) = {
    ctx.error(s"$tree $msg", tree.pos)
    tree
  }

  import collection.mutable

  type InnerFuns = mutable.HashMap[Symbol, DefDef]
  var innerFunctionsOf = mutable.HashMap[Symbol, InnerFuns]()

  def isInnerFunction(sym: Symbol)(implicit ctx: Context): Boolean =
    sym.is(Flags.Method) && sym.owner.is(Flags.Method)

  override def transformDefDef(tree: tpd.DefDef)(
      implicit ctx: Context,
      info: TransformerInfo): tpd.Tree = {
    val ctx0: Context = ctx.withModeBits(Mode.FutureDefsOK)
    val result = {
      implicit val ctx: Context = ctx0

      val sym = tree.symbol
/*      println(s"TREE ${tree.show}")
      println(s"RAW TREE ${tree}")*/
      // TODO: Should we not optimize labels as well?
      if (!isInnerFunction(sym) && !sym.is(Flags.Label)) {
        val (analyzer, optimizeExpressions, transformer) =
          elimCommonSubexpression(ctx.withOwner(tree.symbol))

        val preEmptyTraversal = ListBuffer[List[IdempotentTree]]()
        val postEmptyTraversal = ListBuffer[List[IdempotentTree]]()
        analyzer(tree,
                 tree,
                 tree,
                 Set.empty[Symbol],
                 State() -> (preEmptyTraversal -> postEmptyTraversal),
                 false,
                 false)

        optimizeExpressions()
        val newTree = new TreeMap() {
          override def transform(tree: tpd.Tree)(implicit ctx: Context) =
            transformer(super.transform(tree))
        }.transform(tree)

        if (newTree ne tree)
          println(s"${tree.symbol} after $phaseName became ${newTree.show}")

        newTree match {
          case newDef: DefDef =>
            if (tree ne newDef) newDef
            else tree
          case _ =>
            reportError("ElimCommonSubexpression didn't return a DefDef",
                        newTree)
        }
      } else if (isInnerFunction(sym)) {
        val previousFuns = innerFunctionsOf.get(sym)
        innerFunctionsOf.get(sym.owner) match {
          case Some(currentFuns) =>
            // Add inner functions to outer owners
            previousFuns.foreach(funs => currentFuns ++= funs)
            currentFuns += sym -> tree
          case None =>
            // Reuse previous recursive inner functions
            val newFuns =
              if (previousFuns.isDefined) previousFuns.get
              else mutable.HashMap[Symbol, DefDef]()
            newFuns += (sym -> tree)
            innerFunctionsOf += sym.owner -> newFuns
        }
        tree
      } else tree
    }

    result
  }

  def elimCommonSubexpression: Optimization = (ctx0: Context) => {
    implicit val ctx: Context = ctx0

    /** Contexts that store the OContext for every method. */
    var orderedContexts = mutable.ListBuffer[(OContext, Tree)]()

    /** Replace a tree by either a init or a ref of an optimized valdef. */
    val replacements = mutable.HashMap[Tree, Tree]()

    /** Store the declarations of the optimized valdefs in the beginning of defs. */
    val declarations = mutable.HashMap[Symbol, List[ValDef]]()

    val True: Tree = Literal(Constant(true))
    val False: Tree = Literal(Constant(false))
    def translateCondToIfs(condTree: Tree): Tree = {
      @inline def toIf(cond: Tree,
               booleanOp: String,
               leftTree: Tree,
               rightTree: Tree) = {
        if (booleanOp == "$bar$bar")
          If(leftTree, True, rightTree)
        else if (booleanOp == "$amp$amp")
          If(leftTree, rightTree, False)
        else cond // Don't handle XOR and other possible ops
      }
      def loop(cond: Tree): Tree = {
        cond match {
          case Apply(Select(leftTree, booleanOp), List(rightTree)) =>
            toIf(cond, booleanOp.toString, loop(leftTree), loop(rightTree))
          case TypeApply(Select(leftTree, booleanOp), List(rightTree)) =>
            toIf(cond, booleanOp.toString, loop(leftTree), loop(rightTree))
          case Select(qual, name) =>
            val newQual = translateCondToIfs(qual)
            if (qual == newQual) cond
            else cpy.Select(cond)(newQual, name)
          case Apply(fun, args) =>
            val newFun = translateCondToIfs(fun)
            val newArgs = args.map(translateCondToIfs)
            if (newFun == fun && newArgs == args) cond
            else cpy.Apply(cond)(newFun, newArgs)
          case TypeApply(fun, targs) =>
            val newFun = translateCondToIfs(fun)
            val newTargs = targs.map(translateCondToIfs)
            if (newFun == fun && newTargs == targs) cond
            else cpy.TypeApply(cond)(newFun, newTargs)
          case _ => cond
        }
      }
      val result = loop(condTree)
      if (result == condTree) condTree else result
    }

    def isUnitConstant(tree: Tree) = tree match {
      case Literal(constant) => constant == Constant(())
      case _ => false
    }

    def getFirstInnerTree(from: Tree) = from match {
      case Block(stats2, expr) =>
        if (stats2.isEmpty) expr else stats2.head
      case topLevel => topLevel
    }

    /** Analyze and spot the optimizable expressions in the program. */
    def analyzer(tree: Tree,
                 prev: Tree,
                 topLevel: Tree,
                 methodCache: Set[Symbol],
                 octx: OContext,
                 skipInner: Boolean,
                 skipUnseen: Boolean): OContext = {
      tree match {
        case valDef: ValDef =>
          analyzer(valDef.rhs, valDef, topLevel, methodCache, octx, skipInner, skipUnseen)

        case defDef: DefDef =>
          if (tree == topLevel) {
            val newCache = methodCache + defDef.symbol
            val (state, traversal) =
              analyzer(defDef.rhs, defDef, topLevel, newCache, octx, skipInner, skipUnseen)
            val optimizedState = state.retainOptimizableExpressions
            val newContext = optimizedState -> traversal
            orderedContexts += (newContext -> tree)
            newContext
          } else octx

        case closure: Closure =>
          analyzer(closure.meth, closure, topLevel, methodCache, octx, skipInner, true)

        case block: Block =>
          (block.stats ::: List(block.expr)).foldLeft(octx) {
            (noctx, subTree) =>
              analyzer(subTree, block, topLevel, methodCache, noctx, skipInner, skipUnseen)
          }

        case tryCatch @ Try(expr, cases, finalizer) =>
          val octx1 = analyzer(expr, tryCatch, topLevel, methodCache, octx, skipInner, true)
          val octx2 = cases.foldLeft(octx1)((acc, caseD) =>
            analyzer(caseD, tryCatch, topLevel, methodCache, acc, skipInner, true))
          analyzer(finalizer, tryCatch, topLevel, methodCache, octx2, skipInner, skipUnseen)

        case branch @ If(rawCond, thenp, elsep) =>
          val cond = translateCondToIfs(rawCond)
          val state =
            analyzer(cond, branch, topLevel, methodCache, octx, skipInner, skipUnseen)
          if (isUnitConstant(thenp)) state
          else if (isUnitConstant(elsep)) state
          else {
            val toAnalyze = List(thenp, elsep)
            val analyzed = toAnalyze.map(
              analyzer(_, branch, topLevel, methodCache, state, true, skipUnseen))
            val commonCtx = analyzed.reduceLeft { (accContext, newContext) =>
              // Traversal list is mutable, choose whichever
              accContext._1.intersect(newContext._1) -> newContext._2
            }
            if (skipInner) commonCtx
            else {
              // If it appears in thenp, it appears in elsep
              followInnerFunctions(thenp,
                                   commonCtx,
                                   methodCache,
                                   topLevel,
                                   false,
                                   skipUnseen)
            }
          }

        case tree: Tree =>
          val ctx1 = IdempotentTrees.from(tree) match {
            case Some(idempotent) if !tree.isInstanceOf[Ident] =>
              val (preTraversal, postTraversal) =
                IdempotentTrees.traverseTrees(idempotent)
              val (currentState, traversals) = octx
              if (preTraversal.nonEmpty) {
                val (t1, t2) = traversals
                // Traversals are list buffers
                t1 += preTraversal
                t2 += postTraversal
              }
              val newState = preTraversal.foldLeft(currentState) {
                (state, st) =>
                  val subTree = st.tree
                  val (counters, stats, innerFunsInfo) = state.get
                  val currentCounter = counters.getOrElse(st, 0)
                  if (skipUnseen && currentCounter == 0) state
                  else {
                    val (inits, refs) = stats.getOrElse(st, EmptyIdempotentInfo)
                    val (newInits, newRefs) =
                      if (inits.nonEmpty) inits -> (subTree :: refs)
                      else List(subTree) -> refs
                    val newCounters = counters + (st -> (currentCounter + 1))
                    val newStats = stats + (st -> (newInits -> newRefs))
                    State((newCounters, newStats, innerFunsInfo))
                  }
              }

              newState -> traversals
            case _ =>
              val unfoldedTrees = IdempotentTrees.unfoldArgs(tree)
              unfoldedTrees.foldLeft(octx) { (noctx, nextTree) =>
                analyzer(nextTree,
                         prev,
                         topLevel,
                         methodCache,
                         noctx,
                         skipInner,
                         skipUnseen)
              }
          }
          if (skipInner) ctx1
          else
            followInnerFunctions(tree, ctx1, methodCache, topLevel, skipInner, skipUnseen)
      }
    }

    @inline
    def followInnerFunctions(tree: Tree,
                             ctx1: OContext,
                             cache: Set[Symbol],
                             topLevel: Tree,
                             skipInner: Boolean,
                             skipUnseen: Boolean) = {
      val funsOpt = innerFunctionsOf.get(topLevel.symbol)
      if (funsOpt.isEmpty || funsOpt.get.isEmpty) ctx1
      else {
        val funs = funsOpt.get
        optimizeInnerFunctions(tree, ctx1, cache, topLevel, funs, skipInner, skipUnseen)
      }
    }

    @inline
    def optimizeInnerFunctions(tree: Tree,
                               currentCtx: OContext,
                               visitedMethods: Set[Symbol],
                               topLevel: Tree,
                               innerFuns: InnerFuns,
                               skipInner: Boolean,
                               skipUnseen: Boolean) = {
      // Gather the invocations in post-order
      val invocations: List[DefDef] =
        TreesUtils.collectInvocations(tree, innerFuns)

      // Analyze inner functions from the ctx in the first call-site
      invocations.foldLeft(currentCtx) { (octx, defDef) =>
        val defSymbol = defDef.symbol
        // Make sure we don't follow recursive methods
        val updatedOctx = if (!visitedMethods.contains(defSymbol)) {
          val visited = visitedMethods + defSymbol
          analyzer(defDef.rhs, defDef, topLevel, visited, octx, skipInner, skipUnseen)
        } else octx
        innerFuns -= defDef.symbol
        updatedOctx
      }
    }

    /** Decide the optimizable expressions in a family of idempotent trees,
      * that is, all the possible top and sub trees that are idempotent. */
    def pruneShorterTrees(counters: List[(IdempotentTree, Int)]) = {
      if (counters.isEmpty) Nil
      else {
        counters
          .foldLeft(List(counters.head)) { (acc, itreeCounter) =>
            val (parent, parentCounter) = acc.head
            val (itree, childCounter) = itreeCounter
            if (parentCounter == childCounter &&
                parent.tree.existsSubTree(_ == itree.tree)) acc
            else itreeCounter :: acc
          }
          .map(_._1)
      }
    }

    /** Optimize a candidate and return its declaration, assignation and ref. */
    @inline def optimize(cand: IdempotentTree): Optimized = {
      val name = ctx.freshName("cse$$").toTermName
      val flags = Flags.Synthetic | Flags.Mutable
      val rhs = cand.tree
      val (tpe, pos) = (rhs.tpe, rhs.pos)
      val symbol = ctx.newSymbol(ctx.owner, name, flags, tpe, coord = pos)
      IdempotentTrees.markIdempotent(symbol)
      val valDef = tpd.ValDef(symbol, tpd.defaultValue(tpe))
      (valDef, tpd.ref(symbol))
    }

    /** Preoptimize recursively the trees by pruning them and selecting the
      * ones that should be optimized. Add these to the global mutable state.
      * To introduce the initializers correctly, introduce the entrypoints
      * before transforming the trees so that we can identify the original ones. */
    val preOptimizer: PreOptimizer = () => {
      def optimizeContext(context: OContext, host: Tree): Unit = {
        val hostSymbol = host.symbol
        val (state, (preTraversal, postTraversal)) = context
        val (counters, stats, _) = state.get
        val optimizedCache = mutable.HashSet[IdempotentTree]()
        val deservesOptimization = mutable.HashSet[IdempotentTree]()

        // TODO(jvican): Remove inefficient pruning with parent analysis
        preTraversal.foreach { forest =>
          val cs = forest.iterator.map(t => t -> counters.getOrElse(t, 0))
          val candidates = cs.filter(_._2 > 1).toList
          deservesOptimization ++= pruneShorterTrees(candidates)
        }

        postTraversal.foreach { forest =>
          val pruned = forest.filter(t => deservesOptimization.contains(t))
          pruned.foreach { itree =>
            if (!optimizedCache.contains(itree)) {
              val (declaration, optimizedRef) = optimize(itree)
              val (inits, refs) = stats(itree)
              val other = declarations.getOrElse(hostSymbol, List.empty[ValDef])
              val updatedDeclarations = declaration :: other
              declarations += hostSymbol -> updatedDeclarations
              val alreadyAssigned = mutable.HashSet.empty[Tree]
              inits.foreach { initTree =>
                // Branches may introduce repeated assignations
                if (!alreadyAssigned.contains(initTree)) {
                  alreadyAssigned += initTree
                  // Apply recursive optimizations in the rhs
                  val updatedRhs = TreesUtils.replace(initTree, replacements)
                  // TODO(jvican): Merge with replace for efficiency
                  TreesUtils.unregisterReplacement(initTree, replacements)
                  val initialization =
                    Block(List(optimizedRef.becomes(updatedRhs)), optimizedRef)
                  replacements += initTree -> initialization
                }
              }
              refs.foreach { ref =>
                // Disable replacement of other optimized sub trees
                TreesUtils.unregisterReplacement(ref, replacements)
                replacements += ref -> optimizedRef
              }
              optimizedCache += itree
            }
          }
        }
      }

      orderedContexts.foreach(p => optimizeContext(p._1, p._2))
      orderedContexts = null
    }

    /** Perform the optimization: add initializers to the top level function
      * in which it was found, add the assignations in the correct position
      * (removing entrypoints if necessary, since they are not useful anymore)
      * and substitute any original appearance of optimized trees by their refs. */
    val transformer: Transformer = {
      case enclosing: DefDef =>
        // Introduce declarations of optimized expressions
        val enclosingSym = enclosing.symbol
        val newTrees = if (declarations.contains(enclosingSym)) {
          val result = declarations(enclosingSym).reverse
          declarations -= enclosingSym
          result
        } else List.empty[ValDef]

        if (newTrees.nonEmpty) {
          if (true) println(i"Introducing ${newTrees.map(_.show)}")
          enclosing match {
            case defDef: DefDef =>
              val finalRhs = enclosing.rhs match {
                case blk@Block(stats, expr) =>
                  cpy.Block(blk)(newTrees ::: stats, expr)
                case singleRhs =>
                  tpd.Block(newTrees, singleRhs)
              }
              val correctTypeRhs = finalRhs.tpe.widenIfUnstable
              cpy.DefDef(defDef)(rhs = finalRhs.withType(correctTypeRhs))
          }
        } else enclosing

      case tree: Tree =>
        val resultingTree = replacements.get(tree) match {
          case Some(replacement) =>
            optimizedTimes = optimizedTimes + 1
            replacement
          case None => tree
        }
        if (debug && (resultingTree ne tree))
          println(s"Rewriting ${tree.show} to ${resultingTree.show}")
        resultingTree
    }

    (analyzer _, preOptimizer, transformer)
  }

  override def transformUnit(tree: tpd.Tree)(implicit ctx: Context,
                                             info: TransformerInfo) = {
    println(s"CSE removed $optimizedTimes expressions")
    tree
  }
}

object IdempotentTrees {

  import ast.tpd._

  /** [[IdempotentTree]]s are wrappers over trees that give us structural
    * equality and therefore the ability to compare different trees with
    * the same shape. It gives us a unique representation of a tree. */
  class IdempotentTree(val tree: tpd.Tree)(implicit ctx: Context) {

    import scala.util.hashing.MurmurHash3.{seqHash, mix}

    /** Witness of structural equality by inspecting the tree */
    def idempotentHashCode(t: Tree)(implicit ctx: Context): Int = {
      t match {
        case EmptyTree => EmptyTree.hashCode()
        case _: This => t.symbol.hashCode()
        case s: Super =>
          // NOTE: super[M1] and super[M2] give the same symbol because mix is `TypeName`
          mix(s.qual.hashCode(), s.mix.hashCode)
        case _: Ident => t.symbol.hashCode()
        case Literal(constant) =>
          // Note that `constant.tag` must be unique
          if (constant.value == null) 0
          else mix(constant.value.hashCode(), constant.tag)
        case Select(qual, name) =>
          mix(name.hashCode(), idempotentHashCode(qual))
        case Apply(fun1, args1) =>
          val idempotents = seqHash(args1.map(idempotentHashCode))
          mix(idempotentHashCode(fun1), idempotents)
        case TypeApply(fun1, targs1) =>
          val idempotents = seqHash(targs1.map(idempotentHashCode))
          mix(idempotentHashCode(fun1), idempotents)
        case t: TypeTree =>
          // TODO(jvican): This is fragile, check with Dima
          t.tpe.widenDealias.hashCode()
        case _ =>
          throw new Error("hashCode on IdempotentTree failed")
          0 // impossible case
      }
    }

    override def hashCode(): Int = idempotentHashCode(this.tree)

    /** Compare idempotent trees by structural equality */
    override def equals(that: Any): Boolean = that match {
      case thatIdempotent: IdempotentTree =>
        this.hashCode() == thatIdempotent.hashCode()
      case _ => false
    }

    override def toString = this.tree.toString
  }

  import ast.tpd._

  // Never call directly without having checked that it's indeed idempotent
  def apply(tree: Tree)(implicit ctx: Context): IdempotentTree =
    new IdempotentTree(tree)

  def from(tree: Tree)(implicit ctx: Context): Option[IdempotentTree] =
    if (isIdempotent(tree)) Some(new IdempotentTree(tree)) else None

  def markIdempotent(sym: Symbol)(implicit ctx: Context) =
    ctx.idempotencyPhase
      .asInstanceOf[IdempotencyInference]
      .markAsIdempotent(sym)

  def invalidMethodRef(sym: Symbol)(implicit ctx: Context): Boolean =
    ctx.idempotencyPhase
      .asInstanceOf[IdempotencyInference]
      .invalidMethodRef(sym)

  def isIdempotent(tree: Tree)(implicit ctx: Context): Boolean =
    ctx.idempotencyPhase.asInstanceOf[IdempotencyInference].isIdempotent(tree)

  /** Unfold the tree and get the closest subtrees prone to be optimized. */
  def unfoldArgs(tree: Tree)(implicit ctx: Context): List[Tree] = {
    def nextValidQual(t: Tree): Tree = {
      t match {
        case s: Select =>
          val sym = s.symbol
          val isMethod = sym.is(Flags.Method)
          val isValid = (isMethod && sym.info.isParameterless) || (!isMethod)
          if (isValid) s else nextValidQual(s.qualifier)
        case _ => t
      }
    }
    tree match {
      case Select(qual, _) => List(nextValidQual(qual))
      case TypeApply(qual, targs) => nextValidQual(qual) :: targs
      case Apply(qual, args) => nextValidQual(qual) :: args
      case Pair(left, right) => List(left, right)
      case Typed(expr, tpt) => List(expr)
      case _ => Nil
    }
  }

  /** Collects all the valid idempotent sub trees, including the original tree.
    * NOTE: If you modify it, change also the semantics of `isIdempotent`. */
  def traverseTrees(t1: IdempotentTree)(
      implicit ctx: Context): (List[IdempotentTree], List[IdempotentTree]) = {
    def collectValid(tree: Tree, canBranch: Boolean = false)
      : (List[IdempotentTree], List[IdempotentTree]) = {
      tree match {
        // A top-level parameterless method may be invoked without `Apply`
        case i: Ident
            if i.symbol.is(Flags.Method) &&
              i.symbol.info.isParameterless && tree == t1.tree =>
          val itree = List(IdempotentTrees(i))
          itree -> itree

        case Ident(_) | Literal(_) | This(_) | EmptyTree => Nil -> Nil

        case Super(_, _) =>
          if (!canBranch) {
            val itree = List(IdempotentTrees(tree))
            itree -> itree
          } else Nil -> Nil

        case Select(qual, _) =>
          val traversalsSubTrees = collectValid(qual, canBranch = true)
          if (!canBranch) traversalsSubTrees
          else {
            val (preTraversal, postTraversal) = traversalsSubTrees
            val itree = IdempotentTrees(tree)
            (itree :: preTraversal, postTraversal ::: List(itree))
          }

        case TypeApply(fn, _) =>
          val traversalsSubTrees = collectValid(fn)
          if (canBranch) {
            val (preTraversal, postTraversal) = traversalsSubTrees
            val itree = IdempotentTrees(tree)
            (itree :: preTraversal, postTraversal ::: List(itree))
          } else traversalsSubTrees

        case Apply(fn, args) =>
          val traversalsFn = collectValid(fn, canBranch = false)
          val collectedArgs = args.map(a => collectValid(a, canBranch = true))
          val e = List.empty[IdempotentTree]
          val traversalArgs = collectedArgs.foldLeft(e -> e) { (acc, ts) =>
            val (preTraversal1, postTraversal1) = acc
            val (preTraversal2, postTraversal2) = ts
            (preTraversal1 ++ preTraversal2) -> (postTraversal1 ++ postTraversal2)
          }
          val preTraversal = traversalsFn._1 ++ traversalArgs._1
          val postTraversal = traversalsFn._2 ++ traversalArgs._2
          if (canBranch) {
            val itree = IdempotentTrees(tree)
            (itree :: preTraversal, postTraversal ::: List(itree))
          } else preTraversal -> postTraversal

        case _ =>
          sys.error(s"INVARIANT BROKEN: wrong idempotent tree $tree")
      }
    }
    collectValid(t1.tree, canBranch = true)
  }

}

object TreesUtils {

  import tpd.{Tree, cpy}
  import scala.collection.mutable

  /** Replace an **idempotent** subtree by a reference to another new tree. */
  def replace(tree: Tree, replacements: mutable.HashMap[Tree, Tree])(
    implicit ctx: Context) = {
    def loop(tree: Tree, topLevel: Boolean = false): Tree = {
      tree match {
        case _: Tree if replacements.contains(tree) =>
          // Exactly equal trees return the original reference
          if (topLevel) tree else replacements(tree)
        case Select(qual, name) => cpy.Select(tree)(loop(qual), name)
        case TypeApply(fn, targs) => cpy.TypeApply(tree)(loop(fn), targs)
        case Apply(fn, args) =>
          val replacedArgs = args.map(a => loop(a))
          cpy.Apply(tree)(loop(fn), replacedArgs)
        case t => t
      }
    }
    loop(tree, topLevel = true)
  }

  /** Delete a targeted already-known **idempotent** subtree. */
  def unregisterReplacement(tree: Tree, replacements: mutable.HashMap[Tree, Tree])(
      implicit ctx: Context) = {
    def loop(tree: Tree): Unit = {
      tree match {
        case _: Tree if replacements.contains(tree) => replacements -= tree
        case Select(qual, name) => loop(qual)
        case TypeApply(fn, targs) => loop(fn)
        case Apply(fn, args) =>
          args.foreach(loop)
          loop(fn)
        case t =>
      }
    }
    loop(tree)
  }

  import tpd._

  /** Depth-first tree traversal that collects `DefDef`s from method invocations.
    * It ignores `TypeTree`s and follows the same semantics as `analyze`. */
  def collectInvocations(tree: Tree,
                         innerFuns: mutable.HashMap[Symbol, DefDef])(
      implicit ctx: Context): List[DefDef] = {
    val visited = mutable.HashSet[Symbol]()

    @inline def collectL(trees: List[Tree], acc: List[DefDef]): List[DefDef] =
      trees.foldLeft(acc)((acc, t) => collect(t, acc))

    def collect(tree: Tree, acc: List[DefDef]): List[DefDef] = tree match {
      case Ident(_) =>
        val sym = tree.symbol
        if (sym.is(Flags.Method) && !visited.contains(sym)) {
          visited += sym
          innerFuns.get(sym).toList
        } else Nil

      case Select(qualifier, name) =>
        val sym = tree.symbol
        val defsInvokedInQual = collect(qualifier, acc)
        if (!visited.contains(sym)) {
          visited += sym
          innerFuns.get(sym).toList ++ defsInvokedInQual
        } else defsInvokedInQual

      case Super(qual, mix) => collect(qual, acc)
      case Apply(fun, args) =>
        val sym = tree.symbol
        val funInvocations = collect(fun, acc)
        val funArgsInvokedDefs = collectL(args, funInvocations)
        if (!visited.contains(sym)) {
          visited += sym
          innerFuns.get(sym).toList ++ funArgsInvokedDefs
        } else funArgsInvokedDefs

      case TypeApply(fun, args) =>
        val sym = tree.symbol
        val funInvocations = collect(fun, acc)
        val funArgsInvokedDefs = collectL(args, funInvocations)
        if (!visited.contains(sym)) {
          visited += sym
          innerFuns.get(sym).toList ++ funArgsInvokedDefs
        } else funArgsInvokedDefs

      case Pair(left, right) => collect(right, collect(left, acc))
      case Typed(expr, tpt) => collect(expr, acc)
      case NamedArg(name, arg) => collect(arg, acc)
      case Assign(_, rhs) => collect(rhs, acc)

      case Block(stats, expr) =>
        collect(expr, collectL(stats, acc))

      case If(cond, thenp, elsep) =>
        val condAcc = collect(cond, acc)
        val defsInvokedInThen = collect(thenp, condAcc)
        val defsInvokedInElse = collect(elsep, condAcc)
        val common = defsInvokedInThen.toSet.intersect(defsInvokedInElse.toSet)

        // Disable optimization for inner functions
        // appearing in only one of the branches
        defsInvokedInElse foreach { invocation =>
          if (!common.contains(invocation))
            innerFuns -= invocation.symbol
        }

        var commonInvocations = List.empty[DefDef]
        defsInvokedInThen foreach { invocation =>
          if (common.contains(invocation))
            commonInvocations = invocation :: commonInvocations
          else innerFuns -= invocation.symbol
        }

        // Return only the invocations in both branches
        commonInvocations

      case tree: ValDef => collect(tree.rhs, acc)

      case tree: DefDef =>
        val vparams = tree.vparamss.foldLeft(acc)((acc, b) => collectL(b, acc))
        collect(tree.rhs, vparams)

      case Closure(env, meth, tpt) =>
        // Disable inner method optimization for those methods
        // invoked for the first time in the body of a lambda
        collect(meth, acc).foreach(innerFuns -= _.symbol)
        acc

      case Match(selector, cases) =>
        val defsInvokedInSelector = collect(selector, acc)
        cases.foldLeft(defsInvokedInSelector)((acc, cs) => collect(cs, acc))

      case CaseDef(pat, guard, body) => collect(body, collect(guard, acc))
      case Return(expr, from) => collect(expr, acc)
      case SeqLiteral(elems, elemtpt) => collectL(elems, acc)
      case Thicket(ts) => collectL(ts, acc)
      case Try(block, handlers, finalizer) =>
        collect(finalizer, collectL(handlers, collect(block, acc)))
          .foreach(innerFuns -= _.symbol)
        acc
      case tree @ Template(constr, parents, self, _) =>
        val defsInvokedInTemplate = collectL(
          tree.body,
          collect(self, collectL(parents, collect(constr, acc))))
        defsInvokedInTemplate.foreach(innerFuns -= _.symbol)
        acc

      case _ => acc
    }

    collect(tree, List.empty[DefDef])
  }

}

object State {

  import tpd.Tree

  /** 0 -> Unseen -> Never used
    * 1 -> Seen
    * 2 -> Optimizable */
  type Counted = Int

  /** Appearances of a given optimizable tree. */
  type Counters = Map[IdempotentTree, Counted]

  /** Symbols where we store the initializers and references to an idem tree. */
  type IdempotentInfo = (List[Tree], List[Tree])

  /** Maps the idempotent trees to the local idempotent information. */
  type IdempotentStats = Map[IdempotentTree, IdempotentInfo]

  /** Inner functions information. */
  type InnerFunsInfo = (Set[tpd.DefDef], Map[IdempotentTree, Symbol])

  private val emptyTrees = List.empty[Tree]
  val EmptyIdempotentInfo: IdempotentInfo = (emptyTrees, emptyTrees)

  def apply(): State = State(
    (Map[IdempotentTree, Counted](),
      Map[IdempotentTree, IdempotentInfo](),
      (Set.empty[tpd.DefDef], Map.empty[IdempotentTree, Symbol]))
  )

}

/** The [[State]] gathers information of the program and stores the set of all
  * the potential optimizable expressions at a concrete point of the traversal.
  * By being immutable, it helps us to support fundamental ops like `intersect`
  * and `diff`, and therefore deal with branches and inner functions. */
case class State(get: (Counters, IdempotentStats, InnerFunsInfo)) extends AnyVal {

  /** Return the common idempotent trees in both states. */
  def intersect(other: State): State = {
    if (this == other) this
    else {
      val (cs, stats, innerFunsInfo) = get
      val (cs2, stats2, innerFunsInfo2) = other.get
      val newCounters = cs.flatMap { pair =>
        val (key, value) = pair
        val value2 = cs2.getOrElse(key, 0)
        // INVARIANT: `cs` never contains values with 0, stop if so
        if (value2 == 0 || value == 0) Nil
        else {
          val occurrences = if (value == 1 && value2 == 1) 1 else value
          List(key -> occurrences)
        }
      }
      val newInfo = stats.flatMap { pair =>
        val (key, value) = pair
        val value2 = stats2.getOrElse(key, EmptyIdempotentInfo)
        // INVARIANT: stats2 can never be empty, stop if so
        if (value2._1.isEmpty) Nil
        else {
          val mixedInits = value._1 ++ value2._1
          val mixedRefs = value._2 ++ value2._2
          List(key -> (mixedInits -> mixedRefs))
        }
      }

      val (visited, initializedIn) = innerFunsInfo
      val (visited2, initializedIn2) = innerFunsInfo2
      val updatedInnerFuns = (visited ++ visited2, initializedIn ++ initializedIn2)
      State((newCounters, newInfo, updatedInnerFuns))
    }
  }

  /** Return the idempotent trees not present in the [[other]] state. */
  def diff(other: State): State = {
    if (this == other) this
    else {
      val (cs, stats, innerFunsInfo) = get
      val (cs2, stats2, innerFunsInfo2) = other.get
      val commonCounters = cs.filter(kv => !cs2.contains(kv._1))
      val commonInfo = stats.filter(kv => !stats2.contains(kv._1))
      val (visited, initializedIn) = innerFunsInfo
      val (visited2, initializedIn2) = innerFunsInfo2
      val updatedInnerFuns = (visited.intersect(visited2),
        initializedIn.filterNot(a => initializedIn2.contains(a._1)))
      State((commonCounters, commonInfo, updatedInnerFuns))
    }
  }

  /** Retain the trees that are optimizable (appeared more than once). */
  def retainOptimizableExpressions: State = {
    val optimizable = get._1.filter(_._2 > 1)
    val optimizableStats = get._2.filterKeys(optimizable.contains)
    State((optimizable, optimizableStats, get._3))
  }

  override def toString =
    s"===\nCOUNTERS (${get._1.size}) :\n${get._1.mkString("\n")}" +
      s"\n\nSTATS (${get._2.size}) :\n${get._2.mkString("\n")}\n===\n"

}
