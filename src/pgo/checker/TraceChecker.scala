package pgo.checker

import pgo.model.{PGoError, SourceLocation}
import CriticalSectionInterpreter.{CSElement, StateStepper}
import pgo.util.{!!!, ById, Description}
import Description._
import com.github.difflib.{DiffUtils, UnifiedDiffUtils}
import pgo.util.TLAExprInterpreter.{TypeError, Unsupported}

import scala.jdk.CollectionConverters._
import scala.collection.mutable

final class TraceChecker(val stateExplorer: StateExplorer) {
  private val traceConsumer = new TraceConsumer
  private val stateSetByElement = mutable.HashMap.empty[ById[TraceElement],stateExplorer.StateSet]
  private val refinedStateSetByElement = mutable.HashMap.empty[ById[TraceElement],stateExplorer.StateSet]

  def consumeTraceElement(traceElement: TraceElement): Unit =
    traceConsumer.consumeTraceElement(traceElement)

  def checkSpeculativePath(): Iterator[Issue] = {
    var stateSet = stateExplorer.initStateSet

    traceConsumer.iterateElementsSafeOrder
      .flatMap { afterElement =>
        val expectedStateSet = stateSet.stepForward(afterElement.archetypeName, afterElement.self)
        expectedStateSet.checkCompatibility(afterElement) match {
          case stateExplorer.NoPlausibleStates =>
            Some(NoPlausibleStates(afterElement = afterElement))
          case stateExplorer.Compatible(refinedStateSet) =>
            stateSet = refinedStateSet
            None
          case stateExplorer.Incompatible(expectedOutcomes) =>
            Some(TraceIncompatibility(
              traceCSElements = afterElement.elements,
              expectedOutcomes = expectedOutcomes,
              beforeStates = stateSet))
        }
      }
  }

  private def combineStateSets(stateSets: IterableOnce[stateExplorer.StateSet]): stateExplorer.StateSet =
    stateExplorer.StateSet(
      stateSets.iterator
        .flatMap(_.states)
        .toSet)

  private def stateSetOf(element: TraceElement): stateExplorer.StateSet =
    stateSetByElement.getOrElseUpdate(ById(element), {
      import traceConsumer._

      def impl(element: TraceElement, visited: Set[ById[TraceElement]]): stateExplorer.StateSet =
        if(visited(ById(element))) {
          stateExplorer.StateSet.empty
        } else {
          refinedStateSetByElement.get(ById(element)) match {
            case Some(refinedStateSet) if element.possiblePredecessors.forall(pred => refinedStateSetByElement.contains(ById(pred))) =>
              refinedStateSet
            case Some(_)|None =>
              stateSetByElement.get(ById(element)) match {
                case Some(stateSet) => stateSet
                case None =>
                  element.possiblePredecessors
                    .map(impl(_, visited + ById(element)))
                    .find(_.states.nonEmpty)
                    .getOrElse {
                      if(element.index == 1) stateExplorer.initStateSet
                      else stateExplorer.StateSet.empty
                    }
                    .stepForward(element.archetypeName, element.self)
              }
          }
        }

      impl(element, Set.empty)
    })

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

  final case class TraceIncompatibility(traceCSElements: List[CSElement], expectedOutcomes: List[StateStepper.StepOutcome], beforeStates: stateExplorer.StateSet) extends Issue(
    d"trace incompatibility with actual trace${
      if(traceCSElements.isEmpty) {
        d"(empty trace)".ensureLineBreakBefore.indented
      } else {
        traceCSElements.view
          .map(_.describe.ensureLineBreakBefore)
          .flattenDescriptions
          .indented
      }
    }\ncompared to expected outcomes:${
      expectedOutcomes.view
        .zipWithIndex
        .map {
          case (StateStepper.StepValid(elements, _), idx) =>
            d"\noutcome ${idx + 1}:" +
              elements.view
                .map(_.describe.ensureLineBreakBefore)
                .flattenDescriptions
                .indented
          case (StateStepper.StepInvalid(elements, err), idx) =>
            d"\noutcome ${idx + 1}:" +
              elements.view
                .map(_.describe.ensureLineBreakBefore)
                .flattenDescriptions
                .indented +
              (err match {
                case err: TypeError => err.describe
                case err: Unsupported => err.describe
                case err => throw err // give up, better to put up a stacktrace
              })
                .ensureLineBreakBefore
                .indented
        }
        .flattenDescriptions
        .indented
    }\nassuming possible previous state(s)\n${
      beforeStates.describe.indented
      }")
}
