package omnilink

import scala.util.Using
import scala.collection.mutable
import org.rogach.scallop.Subcommand
import pgo.model.tla.*
import pgo.util.ArgUtils.given
import pgo.util.TLAExprInterpreter.{
  TLAValue,
  TLAValueFunction,
  TLAValueString,
  TLAValueNumber,
  TLAValueBool,
  TLAValueTuple,
}
import pgo.trans.TLARenderPass

trait GenTLA:
  genTLA: Subcommand =>

  final case class TraceRecord(
      op_start: Int,
      op_end: Int,
      operation_name: String,
      operation: Map[String, upack.Msg],
  ) derives upickle.default.ReadWriter:
    def toTLA(pid: Int): TLAValue =
      TLAValueFunction(
        Map(
          TLAValueString("pid") -> TLAValueNumber(pid),
          TLAValueString("op_start") -> TLAValueNumber(op_start),
          TLAValueString("op_end") -> TLAValueNumber(op_end),
          TLAValueString("operation_name") -> TLAValueString(operation_name),
          TLAValueString("operation") -> TLAValueFunction:
            operation.map: (key, value) =>
              TLAValueString(key) -> msgToTLA(value),
        ),
      )
    end toTLA
  end TraceRecord

  def msgToTLA(msg: upack.Msg): TLAValue =
    msg match
      case upack.Null         => TLAValueString("null")
      case upack.True         => TLAValueBool(true)
      case upack.False        => TLAValueBool(false)
      case upack.Int32(value) => TLAValueNumber(value)
      case upack.Int64(value) =>
        assert(
          value <= Int.MaxValue,
          s"long $value outside int range (${Int.MaxValue})",
        )
        TLAValueNumber(value.toInt)
      case upack.UInt64(value) =>
        assert(
          value <= Int.MaxValue,
          s"long $value outside int range (${Int.MaxValue})",
        )
        TLAValueNumber(value.toInt)
      case upack.Float32(_) | upack.Float64(_) | upack.Binary(_) |
          upack.Ext(_, _) =>
        throw RuntimeException(s"unsupported msgpack value $msg")
      case upack.Str(value) =>
        TLAValueString(value)
      case upack.Arr(value) =>
        TLAValueTuple(value.view.map(msgToTLA).toVector)
      case upack.Obj(value) =>
        TLAValueFunction:
          value.view
            .map: (key, value) =>
              msgToTLA(key) -> msgToTLA(value)
            .toMap
  end msgToTLA

  val specFile = trailArg[os.Path](
    descr = "the TLA+ specification to operate on",
    required = true,
  )
  val logsDir = trailArg[os.Path](
    descr =
      "the path containing log files, into which to write trace validation setup",
    required = true,
  )
  val destDir = opt[os.Path](
    descr = "directory to output TLA+ trace validation (defaults to logs dir)",
    default = Some(logsDir()),
  )

  def run(): Unit =
    val tlaModule = pgo.PGo.parseTLA(specFile())
    val moduleName = tlaModule.name.id
    val tlaValidateFile = destDir() / s"${moduleName}Validate.tla"
    val validateDataFile = destDir() / s"${moduleName}ValidateData.bin"

    val caseList = GenHPP.gatherCaseList(tlaModule)

    // ensure destination dir exists
    os.makeDir.all(destDir())

    val logFiles = os
      .list(logsDir())
      .filter(os.isFile)
      .filter(_.last.endsWith(".log"))
      // for deterministic output, in case the filesystem permutes them
      .sortBy(_.last)

    val variableNames = tlaModule.units
      .collect:
        case TLAVariableDeclaration(variables) =>
          variables.view.map(_.id.id)
      .flatten
    val constants = tlaModule.units
      .collect:
        case TLAConstantDeclaration(constants) =>
          constants
      .flatten

    val traces = logFiles.view.zipWithIndex
      .map: (logFile, idx) =>
        idx -> Using.resource(os.read.inputStream(logFile)): inputStream =>
          val reader = new upack.InputStreamMsgPackReader(inputStream):
            override def getByteSafe(i: Int): Byte =
              if requestUntil(i)
              then throw java.io.EOFException("EOF")
              else super.getByteSafe(i)
          Iterator
            .continually:
              try Some(reader.parse(upickle.default.reader[TraceRecord]))
              catch case _: java.io.EOFException => None
            .takeWhile(_.nonEmpty)
            .flatten
            .to(mutable.ArrayBuffer)
      .toMap
    end traces

    val tracesTLA = TLAValueFunction:
      traces.map: (key, values) =>
        TLAValueNumber(key) -> TLAValueTuple(
          values.view.map(_.toTLA(key)).toVector,
        )
    end tracesTLA

    val opCases = caseList.map: (name, args) =>
      s"__op_name = \"$name\" -> __Spec!$name(${args.map(a => s"__op.$a").mkString(", ")}) /\\ __Action_$name"

    val actionOverridePoints = caseList.map: (name, _) =>
      s"__Action_$name == TRUE"

    val extraVarNames = List("__pc", "__viable_pids", "__action")

    val validateTLAFileContents =
      s"""---- MODULE ${moduleName}Validate ----
         |EXTENDS Integers
         |
         |CONSTANTS ${constants
          .map(TLARenderPass.describeOpDecl)
          .map(_.linesIterator.mkString)
          .mkString(", ")}
         |VARIABLES ${variableNames.mkString(", ")}
         |
         |__Spec == INSTANCE $moduleName
         |
         |VARIABLES ${extraVarNames.mkString(", ")}
         |
         |__Spec_vars == <<${variableNames.mkString(", ")}>>
         |__vars == <<${("__Spec_vars" :: extraVarNames).mkString(", ")}>>
         |__state == [${(variableNames ++ extraVarNames).view
          .map(name => s"$name |-> $name")
          .mkString(", ")}]
         |
         |__tracefile_name == "${moduleName}ValidateData.bin"
         |
         |__TraceOps == INSTANCE __TraceOps
         |
         |__traces == __TraceOps!traces
         |
         |Init ==
         |    /\\ __Spec!Init
         |    /\\ __TraceOps!Init
         |
         |__AbortBehavior ==
         |    UNCHANGED __Spec_vars
         |
         |${actionOverridePoints.mkString("\n\n")}
         |
         |Next ==
         |    \\/ \\E __pid \\in __viable_pids :
         |         LET __event == __traces[__pid][__pc[__pid]]
         |             __op_name == __event.operation_name
         |             __op == __event.operation
         |         IN  \\/ /\\ __op._did_abort
         |                /\\ __action' = __event
         |                /\\ __pc' = [__pc EXCEPT ![__pid] = @ + 1]
         |                /\\ __viable_pids' = __TraceOps!ViablePIDs'
         |                /\\ __AbortBehavior
         |             \\/ /\\ \\lnot __op._did_abort
         |                /\\ __action' = __event
         |                /\\ ${opCases.mkString(
          "CASE ",
          "\n                     [] ",
          "",
        )}
         |                /\\ __pc' = [__pc EXCEPT ![__pid] = @ + 1]
         |                /\\ __viable_pids' = __TraceOps!ViablePIDs'
         |    \\/ __TraceOps!EndCheck
         |====
      """.stripMargin

    // Ensure dependent TLA+ files are copied over
    tlaModule.dependencies.view
      .map(_.name.id)
      .map(name => specFile() / os.up / s"$name.tla")
      .filter(os.exists)
      .filter(os.isFile)
      .foreach: dep =>
        os.copy.over(from = dep, to = destDir() / dep.last)

    // Ensure the TraceOps boilerplate is present
    os.write.over(destDir() / "__TraceOps.tla", data = os.read.stream(os.resource / "__TraceOps.tla"))

    os.write.over(tlaValidateFile, validateTLAFileContents)
    os.write.over(
      destDir() / s"${moduleName}.tla",
      data = os.read.stream(specFile()),
    )
    os.write.over(validateDataFile, tracesTLA.asTLCBinFmtGZIP)
  end run
end GenTLA
