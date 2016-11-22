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
class MinimizeClosures extends MiniPhaseTransform with IdentityDenotTransformer {
  thisTransform =>
  def phaseName: String = "minimizeClosures"
  import tpd._

  override def transformClosure(tree: tpd.Closure)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    val analyzeClouresPhase = ctx.phaseOfClass(classOf[AnalyzeClosures]).asInstanceOf[AnalyzeClosures]
    val acessedFields = analyzeClouresPhase.accessedFileds

    acessedFields.get(tree.meth.symbol) match {
      case Some(acessedFields) if (!tree.meth.symbol.isStatic) =>
        // a non-static method. Let's minimize `this` :-)
        // todo: check if it uses refference equality
        val oldSelect = tree.meth.asInstanceOf[Select]
        val Select(a: This, _) = oldSelect
        def copyAndNullOutFields(t: Tree) = {
          val staticType = t.tpe.widen
          val clone = t.select(nme.clone_).appliedToNone.ensureConforms(staticType)
          val nonMethods = t.tpe.widenDealias.membersBasedOnFlags(EmptyFlags, Flags.Method)
          val fieldsToNullOut = t.tpe.widenDealias.fields.filter(f => f.info.derivesFrom(defn.ObjectClass) && !acessedFields.contains(f.symbol))
          if (fieldsToNullOut.nonEmpty && !acessedFields.exists(x => x.owner == staticType.typeSymbol && (x is Flags.Mutable))) {
            if (!staticType.derivesFrom(defn.JavaCloneableClass)) {
              val symDenot = staticType.typeSymbol.denot.asSymDenotation
              val newInfo = symDenot.info match {
                case t: ClassInfo =>
                  t.derivedClassInfo(classParents = t.classParents.head :: defn.JavaCloneableClass.typeRef :: t.classParents.tail)
              }
              symDenot.copySymDenotation(info = newInfo).installAfter(this)
            }
            val newPrefix = evalOnce(clone) { ref =>
              Block(fieldsToNullOut.map(x =>
                ref.select(x.symbol).becomes(Literal(Constant(null)))
              ).toList, ref)
            }
            newPrefix
          } else t
        }
        tpd.cpy.Closure(tree)(meth = copyAndNullOutFields(a).select(oldSelect.symbol))
      case _ =>
        tree
    }
  }
}

