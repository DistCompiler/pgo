package pgo

import org.scalactic.source.Position
import org.scalatest.funsuite.AnyFunSuite
import pgo.util.TLAExprInterpreter.{TLAValue, TLAValueNumber}

class CheckerTraceTests extends AnyFunSuite {

  Config(specFile = os.pwd / "test" / "files" / "general" / "dqueue.tla")
    .withConstants(
      "NUM_CONSUMERS" -> TLAValueNumber(1),
      "PRODUCER" -> TLAValueNumber(0),
      "BUFFER_SIZE" -> TLAValueNumber(10),
    )
    //.testFile(os.pwd / "test" / "traces" / "dqueue_trace_1.txt")
    .testFile(os.pwd / "test" / "traces" / "dqueue_trace_2.txt")


  case class Config(specFile: os.Path, constants: Map[String,TLAValue] = Map.empty) {
    def withConstants(bindings: (String,TLAValue)*): Config =
      copy(constants = constants ++ bindings)

    def testFile(path: os.Path)(implicit position: Position): Config = {
      test(s"checker ${specFile.relativeTo(os.pwd)}: ${path.relativeTo(os.pwd)}") {
        val errors = PGo.run(
          Seq("tracecheck", "--spec-file", specFile.toString(), "--trace-file", path.toString()) ++
            constants.map { case (bind, value) => s"-C$bind=$value" })
        assert(errors.isEmpty)
      }

      this
    }
  }
}
