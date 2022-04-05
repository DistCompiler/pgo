package pgo

import org.scalactic.source.Position
import org.scalatest.funsuite.AnyFunSuite
import pgo.util.TLAExprInterpreter.{TLAValue, TLAValueBool, TLAValueNumber}

import scala.concurrent.duration.{Duration, MILLISECONDS}

class CheckerTraceTests extends AnyFunSuite {



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
    //.testFile(os.pwd / "test" / "traces" / "proxy_first_server_crashing_TCPMailboxes.txt")
    .testFile(os.pwd / "test" / "traces" / "proxy_no_server_running_TCPMailboxes.txt")
    .testFile(os.pwd / "test" / "traces" / "proxy_second_server_running_TCPMailboxes.txt")

  Config(specFile = os.pwd / "test" / "files" / "general" / "raft.tla")
    .withConstants(
      "NumServers" -> TLAValueNumber(3),
    )
    //.testFile(os.pwd / "test" / "traces" / "raft_3_0_0.txt")
    //.testFile(os.pwd / "test" / "traces" / "raft_3_0_1.txt")
    //.testFile(os.pwd / "test" / "traces" / "raft_3_2_0.txt")
    //.testFile(os.pwd / "test" / "traces" / "raft_3_2_1.txt")
    .withConstants(
      "NumServers" -> TLAValueNumber(5),
    )
    //.testFile(os.pwd / "test" / "traces" / "raft_5_0_0.txt")
    //.testFile(os.pwd / "test" / "traces" / "raft_5_0_1.txt")
    //.testFile(os.pwd / "test" / "traces" / "raft_5_0_2.txt")
    //.testFile(os.pwd / "test" / "traces" / "raft_5_2_0.txt")
    //.testFile(os.pwd / "test" / "traces" / "raft_5_2_1.txt")

  Config(specFile = os.pwd / "test" / "files" / "general" / "dqueue.tla")
    .withConstants(
      "NUM_CONSUMERS" -> TLAValueNumber(1),
      "PRODUCER" -> TLAValueNumber(0),
      "BUFFER_SIZE" -> TLAValueNumber(10),
    )
    //.testFile(os.pwd / "test" / "traces" / "dqueue_trace_1.txt")
    .testFile(os.pwd / "test" / "traces" / "dqueue_trace_2.txt")
    //.testFile(os.pwd / "test" / "traces" / "dqueue_trace_2_bad.txt")

  final case class Config(specFile: os.Path, constants: Map[String,TLAValue] = Map.empty, configPathOpt: Option[os.Path] = None) {
    def withConfig(configPath: os.Path): Config =
      copy(configPathOpt = Some(configPath))

    def withConstants(bindings: (String,TLAValue)*): Config =
      copy(constants = constants ++ bindings)

    def testFile(path: os.Path)(implicit position: Position): Config = {
      test(s"checker ${specFile.relativeTo(os.pwd)}: ${path.relativeTo(os.pwd)}") {
        val startTime = System.currentTimeMillis()
        val errors = PGo.run(
          Seq("tracecheck", "--spec-file", specFile.toString(), "--trace-file", path.toString()) ++
            constants.map { case (bind, value) => s"-C$bind=$value" } ++
            configPathOpt.toList.flatMap { path => Seq("--config-file", path.toString()) })
        val endTime = System.currentTimeMillis()
        val duration = Duration(length = endTime - startTime, unit = MILLISECONDS)
        println(s"took $duration")
        assert(errors.isEmpty)
      }

      this
    }
  }
}
