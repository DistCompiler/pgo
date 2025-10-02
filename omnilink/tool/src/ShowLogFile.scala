package omnilink

import org.rogach.scallop.Subcommand

import pgo.util.ArgUtils.given

trait ShowLogFile:
  showLogFile: Subcommand =>
  val logFile = trailArg[os.Path](descr = "log file to read", required = true)

  def run(): Unit =
    val trace = GenTLA.readLogFile(logFile())
    pprint.pprintln(trace, height = Int.MaxValue)
  end run
end ShowLogFile
