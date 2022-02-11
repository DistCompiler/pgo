package pgo

import org.scalactic.source.Position
import org.scalatest.funsuite.AnyFunSuite
import pgo.checker.CriticalSectionInterpreter
import pgo.model.Definition.ScopeIdentifier
import pgo.model.{Definition, RefersTo, SourceLocation}
import pgo.model.tla._
import pgo.parser.{MPCalParser, TLAParser}
import pgo.trans.MPCalNormalizePass
import pgo.checker.CriticalSectionInterpreter.{EvalState, StateStepper}
import pgo.util.{!!!, ById}
import pgo.util.TLAExprInterpreter.{TLAValue, TLAValueNumber}

import scala.util.Using

class TraversalSmokeTests extends AnyFunSuite {
  checkFile(_ / "general" / "dqueue.tla")(
    constants = Map(
      "NUM_CONSUMERS" -> TLAValueNumber(1),
      "PRODUCER" -> TLAValueNumber(0),
      "BUFFER_SIZE" -> TLAValueNumber(10),
    ),
    archetypeSelves = Map(
      "AConsumer" -> TLAValueNumber(1),
      "AProducer" -> TLAValueNumber(0),
    ),
  )


  def checkFile(pTrans: os.Path => os.Path)(constants: Map[String,TLAValue], archetypeSelves: Map[String,TLAValue])(implicit pos: Position): Unit = {
    val path = pTrans(os.pwd / "test" / "files")
    test(path.relativeTo(os.pwd).toString()) {
      checkUntilDepth(path, depth = 5, constants = constants, archetypeSelves = archetypeSelves)
    }
  }

  def checkUntilDepth(specPath: os.Path, depth: Int, constants: Map[String,TLAValue], archetypeSelves: Map[String,TLAValue]): Unit = {
    Using.Manager { use =>
      val buf = PGo.charBufferFromFile(specPath, use)
      val locUnderlying = new SourceLocation.UnderlyingFile(specPath)
      val tlaModule = TLAParser.readModuleBeforeTranslation(locUnderlying, buf)
      val mpcalBlock = MPCalNormalizePass(
        tlaModule,
        MPCalParser.readBlock(locUnderlying, buf, tlaModule))

      def identifierAsString(ident: ScopeIdentifier): String =
        ident match {
          case Definition.ScopeIdentifierName(name) => name.id
          case Definition.ScopeIdentifierSymbol(symbol) => symbol.symbol.stringReprDefn
        }

      val adjustedConstants: Map[ById[RefersTo.HasReferences],TLAValue] =
        tlaModule.units.view
          .collect { case decl@TLAConstantDeclaration(_) => decl }
          .flatMap { decl =>
            decl.constants.view
              .collect {
                case decl if constants.contains(identifierAsString(decl.identifier)) =>
                  ById(decl) -> constants(identifierAsString(decl.identifier))
              }
          }
          .toMap

      assert(adjustedConstants.size == constants.size, "all configured constants in should exist in the spec")

      val stepper = CriticalSectionInterpreter.StateStepper(mpcalBlock, constants = adjustedConstants)

      val (_, reachableStates) = (0 until  depth).view
        .foldLeft((stepper.initStates.toSet, Set.empty[EvalState])) { (accPair, _) =>
          val (newStates, seenStates) = accPair
          val newNewStates = newStates.flatMap { state =>
            archetypeSelves.view
              .flatMap {
                case (archetypeName, self) =>
                  stepper.step(archetypeName, self)(state)
                    .map {
                      case StateStepper.StepValid(elements, nextState) =>
                        assert(elements.nonEmpty)
                        nextState
                      case StateStepper.StepInvalid(elements, err) =>
                        withClue(elements.mkString("\n") ++ "\n" ++ err.toString) {
                          assert(false); !!!
                        }
                    }
              }
          }
          (newNewStates -- seenStates, newNewStates ++ seenStates)
        }

      assert(reachableStates.nonEmpty)
    }
      .get
  }
}
