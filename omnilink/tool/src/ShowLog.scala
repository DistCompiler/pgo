package omnilink

import scala.collection.mutable
import scala.util.Using

import org.rogach.scallop.Subcommand

import pgo.util.ArgUtils.given

trait ShowLog:
  showLogFile: Subcommand =>

  object scala extends Subcommand("scala"):
    val logFiles =
      trailArg[List[os.Path]](descr = "log file(s) to read", required = true)

    def run(): Unit =
      val noColor = System.getenv("NO_COLOR") match
        case null => false
        case ""   => false
        case _    => true
      logFiles().foreach: logFile =>
        println(logFile)
        val trace = GenTLA.readLogFile(logFile)
        if noColor
        then pprint.PPrinter.BlackWhite.pprintln(trace, height = Int.MaxValue)
        else pprint.pprintln(trace, height = Int.MaxValue)
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
              lines += s"${elem.operation("_op_start").int64} ${elem.operation_name}_start $pid {\"$pid\": ${idx * 2 + 1}}..$elemJs "
              lines += s"${elem.operation("_op_end").int64} ${elem.operation_name}_end $pid {\"$pid\": ${idx * 2 + 2}}..$elemJs"

      os.write(outFile(), data = lines.view.flatMap(line => List(line, "\n")))
    end run
  end tsviz
  addSubcommand(tsviz)
  object porcupine extends Subcommand("porcupine"):
    val logsDir = trailArg[os.Path](
      descr = "directory containing *.log files",
      required = true,
    )
    val outFile = trailArg[os.Path](descr = "output file", required = true)

    final case class Operation(
        clientId: Int,
        input: Map[String, upack.Msg],
        call: Long,
        output: Map[String, ujson.Value],
        `return`: Long,
    ) derives upickle.default.Writer

    def run(): Unit =
      val traces = os
        .list(logsDir())
        .filter(os.isFile)
        .filter(_.last.endsWith(".log"))
        .sortBy(_.last)
        .map(GenTLA.readLogFile)

      val allTimes = mutable.TreeSet[Long]()
      traces.view.flatten
        .foreach: rec =>
          allTimes += rec.operation("_op_start").int64
          allTimes += rec.operation("_op_end").int64

      val shortTime = allTimes.iterator.zipWithIndex.toMap

      val ops = traces.view.zipWithIndex
        .map: (buf, idx) =>
          buf.view.map((_, idx))
        .flatten
        .map: (rec, idx) =>
          Operation(
            clientId = idx,
            input = rec.operation
              .updated("operation_name", upack.Str(rec.operation_name)),
            call = shortTime(rec.operation("_op_start").int64),
            output = Map(),
            `return` = shortTime(rec.operation("_op_end").int64),
          )

      Using.resource(os.write.outputStream(outFile())): out =>
        upickle.writeToOutputStream(ops, out)
    end run
  end porcupine
  addSubcommand(porcupine)

  addValidation:
    subcommand match
      case Some(_) => Right(())
      case None    => Left("provide a command to run")

  def run(): Unit =
    subcommand.get match
      case `scala`     => scala.run()
      case `tsviz`     => tsviz.run()
      case `porcupine` => porcupine.run()
  end run
end ShowLog
