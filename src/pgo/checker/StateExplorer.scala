package pgo.checker

import pgo.model.RefersTo
import pgo.util.{ById, CriticalSectionInterpreter}
import pgo.model.mpcal._
import pgo.util.CriticalSectionInterpreter.{CSAbridged, CSDisorderedAtoms, CSElement, CSRead, CSWrite, StateStepper, EvalState}
import pgo.util.TLAExprInterpreter.TLAValue

import scala.annotation.tailrec

final class StateExplorer(mpcalBlock: MPCalBlock, constants: Map[ById[RefersTo.HasReferences],TLAValue]) { stateExplorer =>
  private val stepper = CriticalSectionInterpreter.StateStepper(mpcalBlock, constants = constants)

  val initStateSet: StateSet = StateSet(states = stepper.initStates.map(StateStepper.StepValid(Nil, _)), clock = VClock.origin)

  final case class StateSet private (states: LazyList[StateStepper.StepOutcome], clock: VClock) {
    def stepForward(archetypeName: String, self: TLAValue): StateSet = {
      val nextClock = clock.inc(archetypeName, self)
      val nextStates = states.flatMap {
        case StateStepper.StepInvalid(_, _) =>
          LazyList.empty
        case StateStepper.StepValid(_, state) =>
          stepper.step(archetypeName, self)(state)
      }
      StateSet(states = nextStates, clock = nextClock)
    }

    def checkCompatibility(traceElement: TraceElement): CompatibilityResult = {
      assert(clock == traceElement.clock)

      @tailrec
      def impl(elements: List[CSElement], expectedElements: List[CSElement]): Option[(CSElement,CSElement)] =
        (elements, expectedElements) match {
          case (Nil, Nil) => None
          case (element :: restElements, expectedElement :: restExpectedElements) =>
            (element, expectedElement) match {
              case (read: CSRead, expectedRead: CSRead) if read == expectedRead =>
                impl(restElements, restExpectedElements)
              case (write: CSWrite, expectedWrite: CSWrite) if write == expectedWrite =>
                impl(restElements, restExpectedElements)
              case (CSAbridged, _) => None
              case (_, CSAbridged) => None
              case (CSDisorderedAtoms(atoms), CSDisorderedAtoms(expectedAtoms)) if atoms == expectedAtoms =>
                impl(restElements, restExpectedElements)
              case (_, CSDisorderedAtoms(expectedAtoms)) if elements.view.take(expectedAtoms.size).toSet == expectedAtoms =>
                impl(elements.drop(expectedAtoms.size), restExpectedElements)
              case (element, expectedElement) =>
                Some((element, expectedElement))
            }
          case (Nil, expectedElement :: _) =>
            Some((CSAbridged, expectedElement))
          case (element :: _, Nil) =>
            Some((element, CSAbridged))
        }

      if(states.isEmpty) {
        NoPlausibleStates
      } else {
        val results = states
          .map {
            case outcome@StateStepper.StepValid(elements, _) =>
              impl(elements, traceElement.elements) match {
                case None =>
                  Compatible(copy(states = LazyList(outcome)))
                case Some((traceCSElement, expectedCSElement)) =>
                  Incompatible(traceCSElement, expectedCSElement)
              }
            case StateStepper.StepInvalid(elements, _) =>
              impl(elements, traceElement.elements) match {
                case None =>
                  Compatible(copy(states = LazyList.empty))
                case Some((traceCSElement, expectedCSElement)) =>
                  Incompatible(traceCSElement, expectedCSElement)
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
          results
            .collectFirst {
              case incompatible: Incompatible => incompatible
            }
            .get
        }
      }
    }
  }

  sealed abstract class CompatibilityResult
  case object NoPlausibleStates extends CompatibilityResult
  final case class Compatible(refinedStateSet: stateExplorer.StateSet) extends CompatibilityResult
  final case class Incompatible(traceCSElement: CSElement, expectedCSElement: CSElement) extends CompatibilityResult
}
