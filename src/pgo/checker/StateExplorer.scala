package pgo.checker

import pgo.model.{RefersTo, SourceLocation}
import pgo.util.{ById, Description}
import pgo.model.mpcal._
import CriticalSectionInterpreter.{CSAbridged, CSCrash, CSDisorderedAtoms, CSElement, CSRead, CSWrite, StateStepper}
import pgo.util.TLAExprInterpreter.{TLAValue, TypeError, Unsupported}
import Description._
import pgo.model.tla.TLANode

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
      assert(clock(traceElement.clockKey) == traceElement.clock(traceElement.clockKey))

      @tailrec
      def impl(elements: List[CSElement], expectedElements: List[CSElement], commonPrefixAcc: List[CSElement]): Option[(List[CSElement],List[CSElement],List[CSElement])] =
        (elements, expectedElements) match {
          case (Nil, Nil) => None
          case (element :: restElements, expectedElement :: restExpectedElements) =>
            (element, expectedElement) match {
              case (read: CSRead, expectedRead: CSRead) if read == expectedRead =>
                impl(restElements, restExpectedElements, commonPrefixAcc = expectedRead :: commonPrefixAcc)
              case (write: CSWrite, expectedWrite: CSWrite) if write == expectedWrite =>
                impl(restElements, restExpectedElements, commonPrefixAcc = expectedWrite :: commonPrefixAcc)
              case (CSAbridged, _) => None
              case (_, CSAbridged) => None
              case (CSDisorderedAtoms(atoms), expected@CSDisorderedAtoms(expectedAtoms)) if atoms == expectedAtoms =>
                impl(restElements, restExpectedElements, commonPrefixAcc = expected :: commonPrefixAcc)
              case (_, expected@CSDisorderedAtoms(expectedAtoms)) if elements.view.take(expectedAtoms.size).toSet == expectedAtoms =>
                impl(elements.drop(expectedAtoms.size), restExpectedElements, commonPrefixAcc = expected :: commonPrefixAcc)
              case (element, expectedElement) =>
                Some((elements, expectedElements, commonPrefixAcc.reverse))
            }
          case _ =>
            Some(elements, expectedElements, commonPrefixAcc.reverse)
        }

      if(states.isEmpty) {
        NoPlausibleStates
      } else {
        val results = states
          .map {
            case outcome@StateStepper.StepValid(elements, _) =>
              impl(traceElement.elements, elements, commonPrefixAcc = Nil) match {
                case None =>
                  Compatible(copy(states = LazyList(outcome)))
                case Some((traceCSElements, expectedCSElements, commonPrefix)) =>
                  Incompatible(
                    traceCSElements = traceCSElements,
                    expectedCSElements = expectedCSElements,
                    commonPrefix = commonPrefix)
              }
            case StateStepper.StepInvalid(elements, err) =>
              impl(traceElement.elements, elements, commonPrefixAcc = Nil) match {
                case None =>
                  Compatible(copy(states = LazyList.empty))
                case Some((traceCSElements, expectedCSElements, commonPrefix)) =>
                  Incompatible(
                    traceCSElements = traceCSElements,
                    expectedCSElements = expectedCSElements :+ CSCrash {
                      err match {
                        case err: TypeError => err.describe
                        case err: Unsupported => err.describe
                        case err => throw err
                      }
                    },
                    commonPrefix = commonPrefix)
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

      val statesDesc =
        if(states.isEmpty) {
          d"no known states"
        } else if(states.size == 1) {
          describeState(states.head)
        } else {
          d"either\n${
            states.view
              .map(describeState)
              .map(_.indented)
              .separateBy(d"\nor\n")
          }"
        }

      d"at clock\n${
        clock.describe.indented
      }\n$statesDesc"
    }
  }

  sealed abstract class CompatibilityResult
  case object NoPlausibleStates extends CompatibilityResult
  final case class Compatible(refinedStateSet: stateExplorer.StateSet) extends CompatibilityResult
  final case class Incompatible(traceCSElements: List[CSElement], expectedCSElements: List[CSElement], commonPrefix: List[CSElement]) extends CompatibilityResult
}
