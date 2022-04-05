package pgo.checker

import pgo.model.RefersTo
import pgo.util.{ById, Description}
import pgo.model.mpcal._
import CriticalSectionInterpreter.{CSAbridged, CSDisorderedAtoms, CSElement, CSRead, CSWrite, StateStepper}
import pgo.util.TLAExprInterpreter.{TLAValue, TypeError, Unsupported}
import Description._

import scala.annotation.tailrec

final class StateExplorer(mpcalBlock: MPCalBlock, constants: Map[ById[RefersTo.HasReferences],TLAValue]) { stateExplorer =>
  private val stepper = CriticalSectionInterpreter.StateStepper(mpcalBlock, constants = constants)

  val initStateSet: StateSet = StateSet(
    states = stepper.initStates
      .view
      .map(StateStepper.StepValid(Nil, _))
      .map(OutcomeWrapper)
      .toSet)

  final case class OutcomeWrapper(val outcome: StateStepper.StepOutcome) {
//    override def equals(obj: Any): Boolean =
//      obj match {
//        case obj: OutcomeWrapper =>
//          (outcome, obj.outcome) match {
//            case (StateStepper.StepValid(_, leftState), StateStepper.StepValid(_, rightState)) => leftState == rightState
//            case (StateStepper.StepInvalid(_, leftErr), StateStepper.StepInvalid(_, rightErr)) => leftErr == rightErr
//            case _ => false
//          }
//        case _ => false
//      }
//
//    override def hashCode(): Int =
//      outcome match {
//        case StateStepper.StepValid(_, nextState) =>
//          nextState.hashCode()
//        case StateStepper.StepInvalid(_, err) =>
//          err.hashCode()
//      }
  }

  object OutcomeWrapper extends (StateStepper.StepOutcome => OutcomeWrapper) {
    def apply(outcome: StateStepper.StepOutcome): OutcomeWrapper = new OutcomeWrapper(outcome)
  }

  final case class StateSet private (states: Set[OutcomeWrapper]) {
    def stepForward(archetypeName: String, self: TLAValue): StateSet = {
      val nextStates = states.view
        .map(_.outcome)
        .flatMap {
          case StateStepper.StepInvalid(_, _) =>
            LazyList.empty
          case StateStepper.StepValid(_, state) =>
            stepper.step(archetypeName, self)(state)
        }
        .map(OutcomeWrapper)
        .toSet

      StateSet(states = nextStates)
    }

    def checkCompatibility(traceElement: TraceElement): CompatibilityResult = {
      //assert(clock(traceElement.clockKey) == traceElement.clock(traceElement.clockKey))

      @tailrec
      def tracesCorrespond(elements: List[CSElement], expectedElements: List[CSElement]): Boolean =
        (elements, expectedElements) match {
          case (Nil, Nil) => true
          case (element :: restElements, expectedElement :: restExpectedElements) =>
            (element, expectedElement) match {
              case (read: CSRead, expectedRead: CSRead) if read == expectedRead =>
                tracesCorrespond(restElements, restExpectedElements)
              case (write: CSWrite, expectedWrite: CSWrite) if write == expectedWrite =>
                tracesCorrespond(restElements, restExpectedElements)
              case (CSAbridged, _) => true
              case (_, CSAbridged) => true
              case (CSDisorderedAtoms(atoms), CSDisorderedAtoms(expectedAtoms)) if atoms == expectedAtoms =>
                tracesCorrespond(restElements, restExpectedElements)
              case (_, CSDisorderedAtoms(expectedAtoms)) if elements.view.take(expectedAtoms.size).toSet == expectedAtoms =>
                tracesCorrespond(elements.drop(expectedAtoms.size), restExpectedElements)
              case _ =>
                false
            }
          case _ =>
            false
        }

      if(states.isEmpty) {
        NoPlausibleStates
      } else {
        val results = states.view
          .map(_.outcome)
          .map {
            case outcome@StateStepper.StepValid(elements, _) =>
              if(tracesCorrespond(traceElement.elements, elements)) {
                Compatible(copy(states = Set(OutcomeWrapper(outcome))))
              } else {
                Incompatible(List(outcome))
              }
            case outcome@StateStepper.StepInvalid(elements, _) =>
              if(tracesCorrespond(traceElement.elements, elements)) {
                Compatible(copy(states = Set.empty))
              } else {
                Incompatible(List(outcome))
//                    err match {
//                      case err: TypeError => err.describe
//                      case err: Unsupported => err.describe
//                      case err => throw err
//                    }
              }
          }

        val compatibles = results.collect {
          case compatible: Compatible => compatible
        }
        if (compatibles.nonEmpty) {
          compatibles.reduce { (left, right) =>
            Compatible(left.refinedStateSet.copy(states = left.refinedStateSet.states ++ right.refinedStateSet.states))
          }
        } else {
          Incompatible(
            expectedOutcomes = results
              .collect {
                case incompatible: Incompatible => incompatible
              }
              .flatMap(_.expectedOutcomes)
              .toList)
        }
      }
    }

    def withAdditionalStates(states: IterableOnce[StateStepper.StepOutcome]): StateSet =
      copy(states = this.states ++ states.iterator.map(OutcomeWrapper))

    def union(other: StateSet): StateSet =
      copy(states = states union other.states)

    def describe: Description = {
      def guessPositionFromElements(elements: List[CSElement]): Description =
        elements.lastOption match {
          case None => d"(insufficient information to calculate position)"
          case Some(element) =>
            d"${element.sourceLocation.longDescription}"
        }

      def describeState(outcome: StateStepper.StepOutcome): Description =
        outcome match {
          case StateStepper.StepValid(elements, nextState) =>
            d"${nextState.describe} near ${guessPositionFromElements(elements)}"
          case StateStepper.StepInvalid(_, err) =>
            err match {
              case err: TypeError => err.describe
              case err: Unsupported => err.describe
              case err => throw err // give up, better to put up a stacktrace
            }
        }

      if(states.isEmpty) {
        d"no known states"
      } else if(states.size == 1) {
        describeState(states.head.outcome)
      } else {
        d"either\n${
          states.view
            .map(_.outcome)
            .map(describeState)
            .map(_.indented)
            .separateBy(d"\nor\n")
        }"
      }
    }
  }

  object StateSet {
    val empty: StateSet = new StateSet(states = Set.empty)
  }

  sealed abstract class CompatibilityResult
  case object NoPlausibleStates extends CompatibilityResult
  final case class Compatible(refinedStateSet: stateExplorer.StateSet) extends CompatibilityResult
  final case class Incompatible(expectedOutcomes: List[StateStepper.StepOutcome]) extends CompatibilityResult
}
