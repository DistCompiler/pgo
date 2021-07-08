package pgo

import org.scalacheck.{Arbitrary, Gen, Prop}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks
import pgo.model.Definition.ScopeIdentifierName
import pgo.model.tla._
import pgo.trans.PCalRenderPass
import pgo.util.Description._
import pgo.util.TLAExprInterpreter

import scala.collection.mutable

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

            val errs = PGo.run(Seq("gogen", "-s", testFile.toString(), "-o", outFile.toString()))
            assert(errs == Nil)

            def somethingBadHappened(): Unit = {
              os.makeDir.all(os.pwd / "fuzz_output")
              val testOut = os.temp.dir(dir = os.pwd / "fuzz_output", deleteOnExit = false)
              println(s"something bad happened. saving test to $testOut")
              os.copy.over(from = workDir, to = testOut)
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

  lazy val trueRandomExprGen: Gen[TLAExpression] = locally {
    val cache = mutable.WeakHashMap[Int,Gen[TLAExpression]]()

    val zeroSizePrimitiveSyntax: List[Gen[TLAExpression]] =
      List(
        Gen.posNum[Int].map(i => TLANumber(TLANumber.IntValue(i), TLANumber.DecimalSyntax)),
        Gen.identifier.map(TLAString),
      )

    def sizedVariadics(sz: Int): List[Gen[TLAExpression]] = {
      val maxWidth = Integer.max(sz - 1, 0)
      def subArity(opWidth: Int): Int =
        if(opWidth == 0) maxWidth else maxWidth / opWidth

      (for {
        ident <- Gen.identifier
        sub <- sizedAST(maxWidth)
      } yield TLADot(sub, TLAIdentifier(ident))) ::
        (if(maxWidth >= 3) {
          List(Gen.listOfN(3, sizedAST(subArity(3))).map {
            case List(cond, tval, fval) =>
              TLAIf(cond, tval, fval)
          })
        } else Nil) ::: // TODO: TLACase on
        (Gen.oneOf(0 to maxWidth).flatMap { elemCount =>
          Gen.listOfN(elemCount, sizedAST(subArity(elemCount)))
            .map(TLASetConstructor)
        }) :: // TODO: TLASetRefinement on
        (Gen.oneOf(0 to maxWidth).flatMap { elemCount =>
          Gen.listOfN(elemCount, sizedAST(subArity(elemCount)))
            .map(TLATuple)
        }) ::
        (if(maxWidth >= 1) {
          List(Gen.oneOf(1 to maxWidth).flatMap { elemCount =>
            for {
              elems <- Gen.listOfN(elemCount, sizedAST(subArity(elemCount)))
              names <- Gen.listOfN(elemCount, Gen.identifier)
            } yield TLARecordConstructor((names zip elems).map {
              case (name, elem) => TLARecordConstructorField(TLAIdentifier(name), elem)
            })
          })
        } else Nil) :::
        (if(maxWidth >= 1) {
          List(Gen.oneOf(1 to maxWidth).flatMap { elemCount =>
            for {
              elems <- Gen.listOfN(elemCount, sizedAST(subArity(elemCount)))
              names <- Gen.listOfN(elemCount, Gen.identifier)
            } yield TLARecordSet((names zip elems).map {
              case (name, elem) => TLARecordSetField(TLAIdentifier(name), elem)
            })
          })
        } else Nil) :::
        BuiltinModules.builtinModules.values.view
          .filter { mod =>
            (mod ne BuiltinModules.Reals) &&
              (mod ne BuiltinModules.Bags) &&
              (mod ne BuiltinModules.TLC) &&
              (mod ne BuiltinModules.Peano) &&
              (mod ne BuiltinModules.ProtoReals)
          }
          .flatMap(_.members)
          .filter(_.arity <= maxWidth)
          .map { op =>
            Gen.listOfN(op.arity, sizedAST(subArity(op.arity))).map { exprs =>
              if(op.arity == 0) {
                TLAGeneralIdentifier(op.identifier.asInstanceOf[ScopeIdentifierName].name, Nil)
                  .setRefersTo(op)
              } else {
                TLAOperatorCall(op.identifier, Nil, exprs)
                  .setRefersTo(op)
              }
            }
          }.toList
    }

    def sizedAST(sz: Int): Gen[TLAExpression] = {
      Gen.lzy {
        cache.getOrElseUpdate(if (sz <= 0) 0 else sz, {
          val elems: List[Gen[TLAExpression]] =
            (if (sz <= 0) zeroSizePrimitiveSyntax else Nil) :::
              sizedVariadics(sz)

          Gen.oneOf(elems.head, elems.tail.head, elems.tail.tail: _*)
        })
      }
    }

    Gen.sized(sizedAST)
  }

}
