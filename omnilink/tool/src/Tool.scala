package omnilink

import scala.collection.{Seq => CSeq}
import org.rogach.scallop.{ScallopConf, Subcommand}

final class Tool(args: CSeq[String]) extends ScallopConf(args):
  banner("OmniLink tool")

  object GenHPPCmd extends Subcommand("gen-hpp"), GenHPP:
    descr("Generate a C++ header file containing struct definitions matching the provided TLA+ specification")
  end GenHPPCmd
  addSubcommand(GenHPPCmd)
  object GenTLACmd extends Subcommand("gen-tla"), GenTLA:
    descr("Generate a TLA+ trace validation setup suitable for validating logs formatter per the corresponding gen-hpp command")
  end GenTLACmd
  addSubcommand(GenTLACmd)
  object TriageCmd extends Subcommand("triage"), Triage:
    descr("Given a binary TESpec formatted counterexample found by TLC, determine whether it matches a known issue")
  end TriageCmd
  addSubcommand(TriageCmd)

  addValidation:
    subcommand match
      case Some(_) => Right(())
      case None    => Left("provide a command to run")

  errorMessageHandler = errMsg =>
    errMsg.linesIterator.foreach: line =>
      println(s"fatal: $line")
    println()
    printHelp()
    throw Tool.ConfigExit(1)
  verify()

  def run(): Unit =
    subcommand.get match
      case GenHPPCmd => GenHPPCmd.run()
      case GenTLACmd => GenTLACmd.run()
      case TriageCmd => TriageCmd.run()
  end run
end Tool

object Tool:
  final case class ConfigExit(errCode: Int) extends RuntimeException(s"exit $errCode")

  def main(args: Array[String]): Unit =
    try
      Tool(args).run()
    catch
      case ConfigExit(errCode) =>
        System.exit(errCode)
end Tool
