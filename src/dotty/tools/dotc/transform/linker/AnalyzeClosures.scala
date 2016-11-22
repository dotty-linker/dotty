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
import dotty.tools.dotc.transform.Summaries.CallWithContext
import dotty.tools.dotc.transform.{BuildCallGraph, TreeTransforms}
import dotty.tools.dotc.transform.TreeTransforms.{MiniPhaseTransform, TransformerInfo, TreeTransform}
import scala.collection.JavaConversions
import collection.mutable
import scala.collection.immutable.::


/** This phase applies rewritings provided by libraries. */
class AnalyzeClosures extends MiniPhaseTransform {
  thisTransform =>
  def phaseName: String = "analyzeClosures"

  var accessedFileds = mutable.HashMap[Symbol, Set[Symbol]]()

  override def transformClosure(tree: tpd.Closure)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    val buildCallGraphPhase = ctx.phaseOfClass(classOf[BuildCallGraph]).asInstanceOf[BuildCallGraph]
    val reachableMethods = buildCallGraphPhase.getReachableMethods
    val starts = reachableMethods.filter(x => x.call.termSymbol == tree.meth.symbol)
    val _visited = new util.IdentityHashMap[CallWithContext, CallWithContext]()
    def isVisited(c: CallWithContext) = _visited.containsKey(c)
    var eqVisited = false
    def markVisited(c: CallWithContext) = {
      if (!eqVisited) eqVisited = c.call.termSymbol eq defn.Object_eq
      _visited.put(c, c)
    }

    starts.foreach(markVisited)
    val queue = collection.mutable.Queue(starts.toSeq: _*)
    while (queue.nonEmpty) { // bfs
      val elem = queue.dequeue()
      elem.outEdges.values.foreach(x =>
        x.iterator.filter(x => !isVisited(x)).foreach{x => markVisited(x); queue.enqueue(x)}
      )
    }

    val touched = JavaConversions.asScalaSet(_visited.keySet())
    val fields = touched.filter(x => !x.call.termSymbol.is(Flags.Method) && x.call.termSymbol.owner.isClass)
    val ownerWhiteList = ctx.owner.ownersIterator.toSet
    val fieldsDefinedOutside = fields.filter{x =>
      val owner = x.call.termSymbol.owner
      ownerWhiteList.contains(owner)
    }.map(x => x.call.termSymbol).toSet

    if (!eqVisited)
      accessedFileds.put(tree.meth.symbol, fieldsDefinedOutside)

    tree
  }
}

