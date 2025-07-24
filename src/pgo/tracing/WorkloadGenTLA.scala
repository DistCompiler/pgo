package pgo.tracing

import scala.util.Using
import scala.util.Try
import pgo.model.tla.*
import pgo.trans.TLARenderPass.describeOpDecl
import scala.util.Failure
import scala.util.Success
import scala.util.chaining.given
import scala.collection.mutable
import pgo.util.TLAExprInterpreter.{
  TLAValue,
  TLAValueFunction,
  TLAValueString,
  TLAValueNumber,
  TLAValueTuple,
  TLAValueBool,
}

object WorkloadGenTLA:
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

  def apply(tlaFile: os.Path, tlaModule: TLAModule, logsDir: os.Path): Unit =
    val moduleName = tlaModule.name.id
    val tlaValidateFile = logsDir / s"${moduleName}Validate.tla"
    val validateDataFile = logsDir / s"${moduleName}ValidateData.bin"

    val caseList = WorkloadGen.gatherCaseList(tlaModule)

    val logFiles = os
      .list(logsDir)
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
      s"__op_name = \"$name\" -> __Spec!$name(${args.map(a => s"__op.$a").mkString(", ")})"

    val extraVarNames = List("__pc", "__viable_pids", "__action")

    val validateTLAFileContents =
      s"""---- MODULE ${moduleName}Validate ----
         |EXTENDS Integers
         |
         |CONSTANTS ${constants
          .map(describeOpDecl)
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
         |Next ==
         |    \\/ \\E __pid \\in __viable_pids :
         |         LET __event == __traces[__pid][__pc[__pid]]
         |             __op_name == __event.operation_name
         |             __op == __event.operation
         |         IN  \\/ /\\ __op._did_abort
         |                /\\ __action' = __event
         |                /\\ __pc' = [__pc EXCEPT ![__pid] = @ + 1]
         |                /\\ __viable_pids' = __TraceOps!ViablePIDs'
         |                /\\ UNCHANGED __Spec_vars
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

    // ensure dependent TLA+ files are copied over
    tlaModule.dependencies.view
      .map(_.name.id)
      .map(name => tlaFile / os.up / s"$name.tla")
      .filter(os.exists)
      .filter(os.isFile)
      .foreach: dep =>
        os.copy.over(from = dep, to = logsDir / dep.last)

    os.write.over(tlaValidateFile, validateTLAFileContents)
    os.write.over(
      logsDir / s"${moduleName}.tla",
      data = os.read.stream(tlaFile),
    )
    os.write.over(validateDataFile, tracesTLA.asTLCBinFmt)
  end apply
end WorkloadGenTLA
