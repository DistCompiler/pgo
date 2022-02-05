package pgo.checker

import pgo.model.{PGoError, SourceLocation}
import pgo.util.CriticalSectionInterpreter.CSElement
import pgo.util.{!!!, ById, Description}
import Description.DescriptionHelper

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
  final case class NoPlausibleStates(element: TraceElement) extends Issue(
    d"no plausible states found for ${element.toString}")
  final case class StatesMismatch(element: TraceElement, existingStateSet: stateExplorer.StateSet, mismatchStateSet: stateExplorer.StateSet) extends Issue(
    d"state mismatch as ${element.toString}")
  final case class TraceIncompatibility(element: TraceElement, traceCSElement: CSElement, expectedCSElement: CSElement) extends Issue(
    d"trace incompatibility at ${element.toString}")

  def checkConsumedElements(): Iterator[Issue] =
    traceConsumer.iterateImmediateSuccessorPairs
      .flatMap {
        case (beforeElement, afterElement) =>
          val expectedAfterState = stateSetOf(beforeElement)
            .stepForward(afterElement.archetypeName, afterElement.self)
          expectedAfterState.checkCompatibility(afterElement) match {
            case stateExplorer.NoPlausibleStates =>
              Some(NoPlausibleStates(afterElement))
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
            case stateExplorer.Incompatible(traceCSElement, expectedCSElement) =>
              Some(TraceIncompatibility(
                afterElement,
                traceCSElement = traceCSElement,
                expectedCSElement = expectedCSElement))
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

object TraceChecker {

}
