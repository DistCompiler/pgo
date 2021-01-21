package pgo

import org.scalactic.source.Position
import org.scalatest.funsuite.AnyFunSuite
import pgo.IntegrationTestingUtils.{testCompileFile, testRunGoCode}

import java.nio.file.Paths
import scala.jdk.CollectionConverters._

class TestCodeGenRunTest extends AnyFunSuite {
  def check(tag: String)(fileName: String, constants: Map[String,String] = Map.empty, expectedStr: String)(implicit pos: Position): Unit =
    test(tag) {
      testCompileFile(
        Paths.get("test", "integration", fileName),
        constants.asJava, compiledFilePath =>
          testRunGoCode(compiledFilePath, expectedStr.linesIterator.toList.asJava))
    }

  check("SimpleEither.tla")(
    fileName = "SimpleEither.tla",
    expectedStr =
      """[1 30]
        |[1 30]
        |[1 30]
        |""".stripMargin)

  check("EitherBothBranches.tla")(
    fileName = "EitherBothBranches.tla",
    expectedStr =
      """[10 20]
        |[10 20]
        |""".stripMargin)

  check("EitherRepeatedExec.tla")(
    fileName = "EitherRepeatedExec.tla",
    expectedStr = "3")

  check("Procedures.tla")(
    fileName = "Procedures.tla",
    constants = Map("N" -> "20", "defaultInitValue" -> "0"),
    expectedStr =
      """1
        |2
        |fizz
        |4
        |buzz
        |fizz
        |7
        |8
        |fizz
        |buzz
        |11
        |fizz
        |13
        |14
        |fizzbuzz
        |16
        |17
        |fizz
        |19
        |buzz
        |""".stripMargin)

  check("ProceduresPSyntax.tla")(
    fileName = "ProceduresPSyntax.tla",
    constants = Map("N" -> "20", "defaultInitValue" -> "0"),
    expectedStr =
      """1
        |2
        |fizz
        |4
        |buzz
        |fizz
        |7
        |8
        |fizz
        |buzz
        |11
        |fizz
        |13
        |14
        |fizzbuzz
        |16
        |17
        |fizz
        |19
        |buzz
        |""".stripMargin)

  check("SingleProcess.tla")(
    fileName = "SingleProcess.tla",
    constants = Map("N" -> "20", "defaultInitValue" -> "0"),
    expectedStr =
      """1
        |2
        |fizz
        |4
        |buzz
        |fizz
        |7
        |8
        |fizz
        |buzz
        |11
        |fizz
        |13
        |14
        |fizzbuzz
        |16
        |17
        |fizz
        |19
        |buzz
        |""".stripMargin)
}
