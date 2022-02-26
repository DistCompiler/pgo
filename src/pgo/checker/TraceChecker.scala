package pgo.checker

import pgo.model.{PGoError, SourceLocation}
import CriticalSectionInterpreter.CSElement
import pgo.util.{!!!, ById, Description}
import Description._

import com.github.difflib.{UnifiedDiffUtils, DiffUtils}

import scala.jdk.CollectionConverters._
import scala.collection.mutable

final class TraceChecker(val stateExplorer: StateExplorer) {
  private val traceConsumer = new TraceConsumer
  private val stateSetByElement = mutable.HashMap.empty[ById[TraceElement],stateExplorer.StateSet]

  def consumeTraceElement(traceElement: TraceElement): Unit =
    traceConsumer.consumeTraceElement(traceElement)

  sealed abstract class Issue(val description: Description) extends PGoError with PGoError.Error {
    override val errors: List[PGoError.Error] = List(this)
    override def sourceLocation: SourceLocation = SourceLocation.unknown
  }
  final case class NoPlausibleStates(afterElement: TraceElement) extends Issue(
    d"no plausible transitions lead to:\n${afterElement.describe.indented}"
  )
    /*d"no plausible transitions found between possible predecessors\n${
      beforeElements.view
        .map(_.describe)
        .flattenDescriptions
        .indented
    }\nand\n${
      afterElement.describe.indented
    }\nassuming preceding state(s)\n${
      beforeStates.view
        .map(_.describe.indented)
        .separateBy(d"\nor\n")
        .indented
    }")*/

  final case class TraceIncompatibility(traceCSElements: List[CSElement], expectedCSElementss: List[List[CSElement]], beforeStates: stateExplorer.StateSet) extends Issue(
    d"trace incompatibility with actual trace${
      if(traceCSElements.isEmpty) {
        d"(empty trace)".ensureLineBreakBefore.indented
      } else {
        traceCSElements.view
          .map(_.describe.ensureLineBreakBefore)
          .flattenDescriptions
          .indented
      }
    }\ndue to${
      val actualTraceLines = traceCSElements.view
        .map(_.describe.ensureLineBreakBefore)
        .flattenDescriptions
        .linesIterator
        .toBuffer

      expectedCSElementss.view
        .distinct
        .map { expectedCSElements =>
            val expectedTraceLines = expectedCSElements.view
              .map(_.describeShort.ensureLineBreakBefore)
              .flattenDescriptions
              .linesIterator
              .toBuffer

            val patch = DiffUtils.diff(actualTraceLines.asJava, expectedTraceLines.asJava)
            val unifiedDiff = UnifiedDiffUtils.generateUnifiedDiff("actual trace", "expected trace", actualTraceLines.asJava, patch, 5)
            d"\ndiff:\n${
              unifiedDiff.asScala.view
                .map(_.toDescription.ensureLineBreakBefore)
                .flattenDescriptions
                .indented
            }"
        }
        .flattenDescriptions
    }\nassuming possible previous state(s)\n${
      beforeStates.describe.indented
    }")

  def checkConsumedElements(): Iterator[Issue] = {
    traceConsumer.iterateElementsPreorder
      //.tapEach { case _ -> elem => println(elem.describe.linesIterator.mkString("\n")) }
      .flatMap {
        case afterElement if afterElement.index == 1 =>
          // nothing to do for index 1, we will auto-calculate predecessors etc for index 2 later
          None
        case afterElement =>
          val expectedAfterState = stateSetOf(afterElement)
          //println(d"${afterElement.describe}\nwith state(s)\n${expectedAfterState.describe.indented}".linesIterator.mkString("\n"))
          import traceConsumer._

          expectedAfterState.checkCompatibility(afterElement) match {
            case stateExplorer.NoPlausibleStates =>
              Some(NoPlausibleStates(afterElement = afterElement))
            case stateExplorer.Compatible(refinedStateSet) =>
              stateSetByElement.get(ById(afterElement)) match {
                case None =>
                case Some(existingSet) =>
                  assert(existingSet.states.size >= refinedStateSet.states.size)
              }
              //println(d"${afterElement.describe}\nrefines:\n${refinedStateSet.describe.indented}".linesIterator.mkString("\n"))
              stateSetByElement(ById(afterElement)) = refinedStateSet
              None
            case stateExplorer.Incompatible(traceCSElements, expectedCSElementss) =>
              Some(TraceIncompatibility(
                traceCSElements = traceCSElements,
                expectedCSElementss = expectedCSElementss,
                beforeStates = combineStateSets(afterElement.possiblePredecessors.map(stateSetOf))))
          }
      }
  }

  private def combineStateSets(stateSets: IterableOnce[stateExplorer.StateSet]): stateExplorer.StateSet =
    stateSets.iterator.foldLeft(stateExplorer.StateSet.empty) { (acc, stateSet) =>
      acc.withAdditionalStates(stateSet.states)
    }

  private def stateSetOf(element: TraceElement): stateExplorer.StateSet =
    stateSetByElement.get(ById(element)) match {
      case Some(stateSet) => stateSet // fast path
      case None =>
        import traceConsumer._
        val setsToAdd = mutable.HashMap.empty[ById[TraceElement], stateExplorer.StateSet]

        def impl(element: TraceElement, visited: Set[ById[TraceElement]]): stateExplorer.StateSet =
          if(visited(ById(element))) {
            stateExplorer.StateSet.empty
          } else {
            stateSetByElement.get(ById(element)) match {
              case Some(stateSet) => stateSet
              case None =>
                val maybeInitStates =
                  if(element.index == 1) Some(stateExplorer.initStateSet)
                  else None

                val computedSet = combineStateSets(element.possiblePredecessors.map(impl(_, visited + ById(element))) ++ maybeInitStates)
                  .stepForward(element.archetypeName, element.self)

                setsToAdd(ById(element)) = setsToAdd
                  .getOrElse(ById(element), stateExplorer.StateSet.empty)
                  .withAdditionalStates(computedSet.states)

                computedSet
            }
          }

        val resultingStateSet = impl(element, Set.empty)
        stateSetByElement ++= setsToAdd
        resultingStateSet
    }
}
