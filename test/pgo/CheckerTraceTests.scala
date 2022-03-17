package pgo

import org.scalactic.source.Position
import org.scalatest.funsuite.AnyFunSuite
import pgo.util.TLAExprInterpreter.{TLAValue, TLAValueNumber, TLAValueBool}

class CheckerTraceTests extends AnyFunSuite {

  Config(specFile = os.pwd / "test" / "files" / "general" / "dqueue.tla")
    .withConstants(
      "NUM_CONSUMERS" -> TLAValueNumber(1),
      "PRODUCER" -> TLAValueNumber(0),
      "BUFFER_SIZE" -> TLAValueNumber(10),
    )
    //.testFile(os.pwd / "test" / "traces" / "dqueue_trace_1.txt")
    .testFile(os.pwd / "test" / "traces" / "dqueue_trace_2.txt")

  Config(specFile = os.pwd / "test" / "files" / "general" / "IndexingLocals.tla")
    .testFile(os.pwd / "test" / "traces" / "IndexingLocals_trace_1.txt")

  Config(specFile = os.pwd / "test" / "files" / "general" / "hello.tla")
    .withConfig(os.pwd / "test" / "traces" / "hello_config.sc")
    .testFile(os.pwd / "test" / "traces" / "hello_simple_trace.txt")
    .testFile(os.pwd / "test" / "traces" / "hello_shared_trace.txt")
    .testFile(os.pwd / "test" / "traces" / "hello_persistent_trace.txt")

  Config(specFile = os.pwd / "test" / "files" / "general" / "proxy.tla")
    .withConstants(
      "NUM_SERVERS" -> TLAValueNumber(2),
      "NUM_CLIENTS" -> TLAValueNumber(1),
      "EXPLORE_FAIL" -> TLAValueBool(true),
      "CLIENT_RUN" -> TLAValueBool(true),
    )
    .testFile(os.pwd / "test" / "traces" / "proxy_all_servers_running_TCPMailboxes.txt")
    .testFile(os.pwd / "test" / "traces" / "proxy_first_server_crashing_TCPMailboxes.txt")
    .testFile(os.pwd / "test" / "traces" / "proxy_no_server_running_TCPMailboxes.txt")
    .testFile(os.pwd / "test" / "traces" / "proxy_second_server_running_TCPMailboxes.txt")

  final case class Config(specFile: os.Path, constants: Map[String,TLAValue] = Map.empty, configPathOpt: Option[os.Path] = None) {
    def withConfig(configPath: os.Path): Config =
      copy(configPathOpt = Some(configPath))

    def withConstants(bindings: (String,TLAValue)*): Config =
      copy(constants = constants ++ bindings)

    def testFile(path: os.Path)(implicit position: Position): Config = {
      test(s"checker ${specFile.relativeTo(os.pwd)}: ${path.relativeTo(os.pwd)}") {
        val errors = PGo.run(
          Seq("tracecheck", "--spec-file", specFile.toString(), "--trace-file", path.toString()) ++
            constants.map { case (bind, value) => s"-C$bind=$value" } ++
            configPathOpt.toList.flatMap { path => Seq("--config-file", path.toString()) })
        assert(errors.isEmpty)
      }

      this
    }
  }
}
