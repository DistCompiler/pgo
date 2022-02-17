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
  final case class NoPlausibleStates(beforeState: stateExplorer.StateSet, beforeElement: TraceElement, afterElement: TraceElement) extends Issue(
    d"no plausible transitions found between\n${
      beforeElement.describe.indented
    }\nand\n${
      afterElement.describe.indented
    }\nassuming preceding state(s)\n${
      beforeState.describe.indented
    }")
  final case class StatesMismatch(element: TraceElement, existingStateSet: stateExplorer.StateSet, mismatchStateSet: stateExplorer.StateSet) extends Issue(
    d"state mismatch at\n${
      element.describe.indented
    }\nbetween\n${
      val left = existingStateSet.describe.linesIterator.toBuffer
      val right = mismatchStateSet.describe.linesIterator.toBuffer
      val patch = DiffUtils.diff(left.asJava, right.asJava)
      val unifiedDiff = UnifiedDiffUtils.generateUnifiedDiff("left", "right", left.asJava, patch, 5)
      unifiedDiff.asScala.view
        .map(_.toDescription.ensureLineBreakBefore)
        .flattenDescriptions
        .indented
    }")
  final case class TraceIncompatibility(fromElement: TraceElement, traceCSElements: List[CSElement], expectedCSElements: List[CSElement], commonPrefix: List[CSElement], beforeState: stateExplorer.StateSet) extends Issue(
    d"trace incompatibility ${
      if(commonPrefix.isEmpty) {
        d"(with no matching prefix) "
      } else {
        d"after matching prefix${
          commonPrefix.view
            .map(_.describe.ensureLineBreakBefore)
            .flattenDescriptions
            .indented
        }\n"
      }
    }between actual\n${
      if(traceCSElements.isEmpty) {
        d"<end of trace>".indented
      } else {
        traceCSElements.view.map(_.describe.ensureLineBreakBefore).flattenDescriptions.indented
      }
    }\nand expected\n${
      if(expectedCSElements.isEmpty) {
        d"<end of trace>".indented
      } else {
        expectedCSElements.view.map(_.describe.ensureLineBreakBefore).flattenDescriptions.indented
      }
    }\nassuming the preceding state(s)\n${
      beforeState.describe.indented
    }")

  def checkConsumedElements(): Iterator[Issue] =
    traceConsumer.iterateImmediateSuccessorPairs
      .flatMap {
        case (beforeElement, afterElement) =>
          val beforeState = stateSetOf(beforeElement)
          val expectedAfterState = beforeState
            .stepForward(afterElement.archetypeName, afterElement.self)
          expectedAfterState.checkCompatibility(afterElement) match {
            case stateExplorer.NoPlausibleStates =>
              Some(NoPlausibleStates(beforeState, beforeElement, afterElement))
            case stateExplorer.Compatible(refinedStateSet) =>
              stateSetByElement.get(ById(afterElement)) match {
                case None =>
                  stateSetByElement(ById(afterElement)) = refinedStateSet
                  None
                case Some(existingAfterState) =>
                  if(existingAfterState == refinedStateSet) {
                    None
                  } else {
                    Some(StatesMismatch(
                      afterElement,
                      existingStateSet = existingAfterState,
                      mismatchStateSet = refinedStateSet))
                  }
              }
            case stateExplorer.Incompatible(traceCSElements, expectedCSElements, commonPrefix) =>
              Some(TraceIncompatibility(
                fromElement = beforeElement,
                traceCSElements = traceCSElements,
                expectedCSElements = expectedCSElements,
                commonPrefix = commonPrefix,
                beforeState = beforeState))
          }
      }

  private def stateSetOf(element: TraceElement): stateExplorer.StateSet = {
    stateSetByElement.getOrElseUpdate(ById(element), {
      if(element.index == 1) {
        stateExplorer.initStateSet
          .stepForward(element.archetypeName, element.self)
      } else {
        !!!
      }
    })
  }
}
