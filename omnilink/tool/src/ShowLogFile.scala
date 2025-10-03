package omnilink

import scala.collection.mutable

import org.rogach.scallop.Subcommand

import pgo.util.ArgUtils.given

trait ShowLogFile:
  showLogFile: Subcommand =>

  object scala extends Subcommand("scala"):
    val logFile = trailArg[os.Path](descr = "log file to read", required = true)

    def run(): Unit =
      val trace = GenTLA.readLogFile(logFile())
      pprint.pprintln(trace, height = Int.MaxValue)
    end run
  end scala
  addSubcommand(scala)
  object tsviz extends Subcommand("tsviz"):
    val logsDir = trailArg[os.Path](
      descr = "directory containing *.log files",
      required = true,
    )
    val outFile = trailArg[os.Path](descr = "output file", required = true)

    def run(): Unit =
      val traces = os
        .list(logsDir())
        .filter(os.isFile)
        .filter(_.last.endsWith(".log"))
        .sortBy(_.last)
        .map(GenTLA.readLogFile)

      val lines = mutable.ListBuffer[String]()
      lines += raw"(?<timestamp>(\d*)) (?<event>\w*) (?<host>\w*) (?<clock>(?!\.\.).*)\.\.(?<json>.*)\n"
      lines += ""

      traces.view.zipWithIndex
        .foreach: (trace, pid) =>
          trace.view.zipWithIndex
            .foreach: (elem, idx) =>
              val elemJs = upickle.write(elem)
              lines += s"${elem.op_start} ${elem.operation_name}_start $pid {\"$pid\": ${idx * 2 + 1}}..$elemJs "
              lines += s"${elem.op_end} ${elem.operation_name}_end $pid {\"$pid\": ${idx * 2 + 2}}..$elemJs"

      os.write(outFile(), data = lines.view.flatMap(line => List(line, "\n")))
    end run
  end tsviz
  addSubcommand(tsviz)

  addValidation:
    subcommand match
      case Some(_) => Right(())
      case None    => Left("provide a command to run")

  def run(): Unit =
    subcommand.get match
      case `scala` => scala.run()
      case `tsviz` => tsviz.run()
  end run
end ShowLogFile
