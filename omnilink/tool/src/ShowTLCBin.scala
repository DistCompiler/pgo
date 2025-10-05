package omnilink

import org.rogach.scallop.{Subcommand, flagConverter}

import pgo.util.ArgUtils.given
import pgo.util.TLAExprInterpreter

trait ShowTLCBin:
  showTLCBin: Subcommand =>

  val noGzip = opt[Boolean](required = false, default = Some(false))
  val binFile = trailArg[os.Path](required = true)

  def run(): Unit =
    val contents = os.read.stream(binFile())
    val tlaValue =
      if noGzip()
      then TLAExprInterpreter.TLAValue.parseFromTLCBinFmt(contents)
      else TLAExprInterpreter.TLAValue.parseFromTLCBinFmtGZIP(contents)
    pprint.pprintln(tlaValue, height = Int.MaxValue)
  end run
end ShowTLCBin
