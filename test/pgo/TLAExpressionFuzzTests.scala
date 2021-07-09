package pgo

import org.scalacheck.{Arbitrary, Gen, Prop}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks
import pgo.model.Definition.ScopeIdentifierName
import pgo.model.DefinitionOne
import pgo.model.tla._
import pgo.trans.PCalRenderPass
import pgo.util.Description._
import pgo.util.{IdMap, IdSet, TLAExprInterpreter}
import pgo.util.TLAExprInterpreter.{TLAValue, TLAValueBool, TLAValueFunction, TLAValueNumber, TLAValueSet, TLAValueString, TLAValueTuple, builtinOperators}

import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.control.NonFatal

class TLAExpressionFuzzTests extends AnyFunSuite with ScalaCheckPropertyChecks {
  implicit override val generatorDrivenConfig: PropertyCheckConfiguration =
    PropertyCheckConfiguration(workers = 1, minSuccessful = 100, maxDiscardedFactor = 10)

  test("TLA+ compiled to Go code behaves like the built-in interpreter (true random ASTs)") {
    val workDir = os.temp.dir()
    val testFile = workDir / "TestBed.tla"
    val outFile = workDir / "testbed.go"
    var degenerateCases = 0
    var cases = 0

    val modFile = workDir / "go.mod"
    os.write(modFile,
      s"""module example.org/testbed
         |
         |go 1.14
         |
         |replace github.com/UBC-NSS/pgo/distsys => ${os.pwd / "distsys"}
         |
         |require github.com/UBC-NSS/pgo/distsys v0.0.0-00010101000000-000000000000
         |""".stripMargin)

    val mainFile = workDir / "main" / "main.go"
    os.makeDir(workDir / "main")
    os.write(mainFile,
      s"""package main
         |
         |import "github.com/UBC-NSS/pgo/distsys"
         |import "example.org/testbed"
         |
         |type dummyDurableStorage struct{}
         |
         |var _ distsys.MPCalDurableStorage = &dummyDurableStorage{}
         |
         |func (d dummyDurableStorage) RecoverResources() (rec *distsys.MPCalDurableStorageRecord, err error) {
         |	return nil, nil
         |}
         |
         |func (d dummyDurableStorage) SnapshotResources(rec *distsys.MPCalDurableStorageRecord) {
         |	// pass
         |}
         |
         |func main() {
         |  ctx, err := distsys.NewMPCalContext(&dummyDurableStorage{})
         |  if err != nil {
         |    panic(err)
         |  }
         |  err = testbed.TestBed(ctx, distsys.NewTLAString("self"), testbed.Constants{})
         |  if err != nil {
         |    panic(err)
         |  }
         |}""".stripMargin)

    try {
      forAll(trueRandomExprGen) { (expr: TLAExpression) =>
        val mpcalSetup =
          d"----MODULE TestBed----\n" +
            d"EXTENDS Integers, Sequences, TLC, FiniteSets\n" +
            d"(* --mpcal TestBed {\n" +
            d"archetype TestBed() {\n" +
            d"lbl: print ${PCalRenderPass.describeExpr(expr)};\n".indented +
            d"} } *)\n" +
            d"\\* BEGIN TRANSLATION\n" +
            d"===="

        val (shouldSkip, expectedBehaviour) = try {
          (false, Right(TLAExprInterpreter.interpret(expr)(env = Map.empty)))
        } catch {
          case err@TLAExprInterpreter.Unsupported() =>
            (true, Left(err))
          case err@TLAExprInterpreter.TypeError() =>
            (false, Left(err))
        }
        whenever(!shouldSkip) {
          cases += 1
          Prop.classify(expectedBehaviour match {
            case Left(_) => degenerateCases += 1; true
            case Right(_) => false
          }, "degenerate", "correct") {
            os.write.over(testFile, data = mpcalSetup.linesIterator.map(line => s"$line\n"))

            def somethingBadHappened(): Unit = {
              os.makeDir.all(os.pwd / "fuzz_output")
              val testOut = os.temp.dir(dir = os.pwd / "fuzz_output", deleteOnExit = false)
              println(s"something bad happened. saving test to $testOut")
              os.copy.over(from = workDir, to = testOut)
            }

            try {
              val errs = PGo.run(Seq("gogen", "-s", testFile.toString(), "-o", outFile.toString()))
              assert(errs == Nil)
            } catch {
              case NonFatal(err) =>
                somethingBadHappened()
                throw err
            }

            os.proc("go", "mod", "download").call(cwd = workDir)

            try {
              os.proc("go", "run", "./main").call(cwd = workDir, mergeErrIntoOut = true, timeout = 15000)
              Prop.passed
            } catch {
              case err: os.SubprocessException =>
                expectedBehaviour match {
                  case Left(_) =>
                    if (err.result.out.text().startsWith("panic: TLA+ type error")) {
                      // that's ok then
                      Prop.passed
                    } else {
                      somethingBadHappened()
                      throw err
                    }
                  case Right(_) =>
                    somethingBadHappened()
                    throw err
                }
            }
          }
        }
      }
    } finally {
      println(s"degenerate cases: $degenerateCases/$cases; ${degenerateCases.toDouble / cases.toDouble * 100}%")
    }
  }

  private def genCombinedASTNodePossibilities(subExprs: List[TLAExpression])(implicit env: IdSet[DefinitionOne], anchorOpt: Option[TLAFunctionSubstitutionPairAnchor]): List[Gen[TLAExpression]] = {
    sealed abstract class GenProvider {
      def genIterator: Iterator[Gen[TLAExpression]]
    }

    implicit class PartialFnGenProvider(iterable: Iterable[Gen[TLAExpression]]) extends GenProvider {
      override def genIterator: Iterator[Gen[TLAExpression]] = iterable.iterator
    }

    implicit class PartialFnIterableGenProvider(gen: Gen[TLAExpression]) extends GenProvider {
      override def genIterator: Iterator[Gen[TLAExpression]] = Iterator.single(gen)
    }

    val builtinModules = BuiltinModules.builtinModules.values.filter { mod =>
      (mod ne BuiltinModules.Reals) &&
        (mod ne BuiltinModules.Bags) &&
        (mod ne BuiltinModules.TLC) &&
        (mod ne BuiltinModules.Peano) &&
        (mod ne BuiltinModules.ProtoReals)
    }

    val cases: Iterator[PartialFunction[List[TLAExpression],GenProvider]] = Iterator(
      { case Nil => for {
          num <- Gen.posNum[Int]
        } yield TLANumber(TLANumber.IntValue(num), TLANumber.DecimalSyntax)
      },
      { case Nil => Gen.asciiPrintableStr.map(TLAString) }, // TODO: consider nonsense w/ unprintable ASCII
      { case Nil if env.exists(_.arity == 0) =>
        env.view
          .filter(_.arity == 0)
          .map { defn =>
            TLAGeneralIdentifier(defn.identifier.asInstanceOf[ScopeIdentifierName].name, Nil)
              .setRefersTo(defn)
          } : Iterable[Gen[TLAExpression]]
      },
      { case Nil =>
        builtinModules.view
          .flatMap(_.members)
          .filter(_.arity == 0)
          .map { defn =>
            TLAGeneralIdentifier(defn.identifier.asInstanceOf[ScopeIdentifierName].name, Nil)
              .setRefersTo(defn)
          } : Iterable[Gen[TLAExpression]]
      },
      { case List(expr: TLAExpression) =>
        for {
          ident <- Gen.identifier
        } yield TLADot(expr, TLAIdentifier(ident))
      },
      { case subExprs: List[TLAExpression] if subExprs.nonEmpty && env.exists(_.arity == subExprs.size) =>
        env.view.filter(_.arity == subExprs.size).map { defn =>
          Gen.const(TLAOperatorCall(defn.identifier, Nil, subExprs).setRefersTo(defn))
        }
      },
      { case subExprs: List[TLAExpression] if subExprs.nonEmpty =>
        builtinModules.view
          .flatMap(_.members)
          .filter(_.arity == subExprs.size)
          .map { defn =>
            TLAOperatorCall(defn.identifier, Nil, subExprs)
              .setRefersTo(defn)
          } : Iterable[Gen[TLAExpression]]
      },
      { case List(cond: TLAExpression, yes: TLAExpression, no: TLAExpression) =>
        Gen.const(TLAIf(cond, yes, no))
      },
      // LET exprs skipped on purpose; we need to understand scoping to get those right, so we leave it to other routines
      { case subExprs: List[TLAExpression] if subExprs.size >= 2 => // require at least one whole case arm's worth
        @tailrec
        def impl(subExprs: List[TLAExpression], armsAcc: List[TLACaseArm]): TLACase =
          subExprs match {
            case Nil => TLACase(armsAcc, None)
            case other :: Nil => TLACase(armsAcc, Some(other))
            case cond :: result :: restArms =>
              impl(restArms, TLACaseArm(cond, result) :: armsAcc)
          }

        Gen.const(impl(subExprs, Nil))
      },
      // skipping function defn for same reason as LET
      { case subExprs: List[TLAExpression] if subExprs.size >= 2 =>
        Gen.const(TLAFunctionCall(subExprs.head, subExprs.tail))
      },
      { case List(from: TLAExpression, to: TLAExpression) =>
        Gen.const(TLAFunctionSet(from, to))
      },
      // TODO: skipping function substitution because complicated
      { case Nil if anchorOpt.nonEmpty =>
        Gen.const(TLAFunctionSubstitutionAt()
          .setRefersTo(anchorOpt.get))
      },
      // skipping quantifiers, again due to scoping
      { case subExprs: List[TLAExpression] =>
        Gen.const(TLASetConstructor(subExprs))
      },
      // skipping set refinement, comprehension due to scoping
      { case subExprs: List[TLAExpression] =>
        Gen.const(TLATuple(subExprs))
      },
      { case subExprs: List[TLAExpression] if subExprs.nonEmpty =>
        for {
          idents <- Gen.listOfN(subExprs.size, Gen.identifier)
        } yield TLARecordConstructor((idents.view zip subExprs).map {
          case ident -> expr => TLARecordConstructorField(TLAIdentifier(ident), expr)
        }.toList)
      },
      { case subExprs: List[TLAExpression] if subExprs.nonEmpty =>
        for {
          idents <- Gen.listOfN(subExprs.size, Gen.identifier)
        } yield TLARecordSet((idents.view zip subExprs).map {
          case ident -> expr => TLARecordSetField(TLAIdentifier(ident), expr)
        }.toList)
      },
    )

    cases.flatMap { fn =>
      fn.unapply(subExprs)
        .map(_.genIterator)
    }
      .flatten
      .toList
  }

  private def forceOneOf[T](gens: List[Gen[T]]): Gen[T] = {
    require(gens.nonEmpty)
    Gen.choose(min = 0, max = gens.size - 1)
      .flatMap(gens)
  }

  lazy val trueRandomExprGen: Gen[TLAExpression] = {
    def impl(size: Int)(implicit env: IdSet[DefinitionOne], anchorOpt: Option[TLAFunctionSubstitutionPairAnchor]): Gen[TLAExpression] =
      for {
        breadth <- Gen.oneOf(0 to size)
        subExprs <- Gen.listOfN(breadth, impl(size / (breadth + 1)))
        expr <- forceOneOf(genCombinedASTNodePossibilities(subExprs))
      } yield expr

    Gen.sized(size => impl(size)(IdSet.empty, None))
  }

}
