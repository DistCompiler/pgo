package pgo.traceview

import scala.collection.View
import scala.util.Using

import pgo.util.TLAExprInterpreter.{
  TLAValue,
  TLAValueBool,
  TLAValueFunction,
  TLAValueNumber,
  TLAValueString,
  TLAValueTuple,
}

final class StateSpace(root: os.zip.ZipRoot) extends AutoCloseable:
  def close(): Unit = root.close()
  val tlaValue =
    TLAValue.parseFromTLCBinFmtGZIP(os.read.stream(root / "counterExample.bin"))
  val traces =
    os.list(root)
      .filter(_.last.endsWith(".log"))
      .sortBy(_.last)
      .map: logFile =>
        Using.resource(os.read.inputStream(logFile)): inputStream =>
          val reader = upack.InputStreamMsgPackReader(inputStream)
          Iterator
            .continually:
              try Some(reader.parse(upack.Msg))
              catch case _: java.io.EOFException => None
            .takeWhile(_.nonEmpty)
            .flatten
            .toIndexedSeq
  end traces
  val compressedTimestamps =
    traces.view.flatten
      .flatMap: msg =>
        msg.obj
          .get(upack.Str("operation"))
          .view
          .flatMap: op =>
            op.obj.get(upack.Str("_op_start")).map(_.int64).toList
              ++ op.obj.get(upack.Str("_op_end")).map(_.int64)
      .toIndexedSeq
      .sorted
      .distinct
      .view
      .zipWithIndex
      .toMap
  end compressedTimestamps
  val pairs: Array[(Long, Long)] =
    tlaValue("pairs").asVector.view
      .map: pair =>
        (pair(1).asString.toLong, pair(2).asString.toLong)
      .toArray
  end pairs

  val allSuccessors: Map[Long, Array[Long]] =
    pairs.groupMap(_._1)(_._2)

  val allPredecessors: Map[Long, Array[Long]] =
    pairs.groupMap(_._2)(_._1)

  val states: Map[Long, TraceRecord] =
    tlaValue("states").asMap
      .map: (k, v) =>
        val fingerprint = k.asString.toLong
        (fingerprint, TraceRecord(fingerprint, v))
  end states

  private val shortIdFromFingerprint: Map[Long, String] =
    val prs = states.view.values
      .map(_.fingerprint)
      .toArray
      .sortInPlace
      .view
      .zipWithIndex
      .map((fingerprint, idx) => (fingerprint, idx.toHexString))
      .toArray

    val maxWidth = prs.view.map(_._2.size).max
    prs.view
      // Note: pad reversed, otherwise we add _trailing_ 0s not leading, which can cause short ID collisions
      .map((fingerprint, id) =>
        (fingerprint, id.reverse.padTo(maxWidth, '0').reverse),
      )
      .toMap
  end shortIdFromFingerprint

  private val fingerprintFromShortId: Map[String, Long] =
    shortIdFromFingerprint.map(_.reverse)

  def deepestStalledStates: List[TraceRecord] =
    val maxDepth = states.view.values.map(_.depth).max
    states.view.values
      .filter(_.depth == maxDepth)
      .toList
  end deepestStalledStates

  sealed abstract class TraceOperation:
    def tlaValue: TLAValue
    def action: TLAValue
    def operation: TLAValue =
      action.get("operation").fold(TLAValueFunction(Map.empty))(identity)

    def operationName: String =
      action.get("operation_name").fold("<init>")(_.asString)
    def operationStart: Int = operation.get("_op_start").fold(0)(_.asInt)
    def operationEnd: Int = operation.get("_op_end").fold(0)(_.asInt)
    def pid: Int = action.get("pid").fold(-1)(_.asInt)
    def didAbort: Boolean =
      operation.get("_did_abort").fold(false)(_.asBoolean)

    def isInitialState: Boolean =
      action == TLAValueTuple(Vector.empty)
    end isInitialState

    def shortId: String

    def titleString: String =
      if isInitialState
      then "initial state"
      else s"$operationName: pid=$pid, span=[$operationStart, $operationEnd]"
    end titleString

    def depthStr: String
    def depthOption: Option[Int]

    def predecessorRecords: View[TraceRecord]

    def descriptiveLabel: String =
      val didAbortPart =
        if didAbort
        then "!!"
        else ""
      s"$shortId $didAbortPart$operationName(${
          if action == TLAValueTuple(Vector())
          then ""
          else
            operation.asMap.view
              .map: (k, v) =>
                val vStr = v.toString
                val truncVStr =
                  if vStr.size > 25
                  then s"${vStr.take(25)}.."
                  else vStr
                (k.asString, truncVStr)
              .filter(_._1 != "_meta")
              .filter(_._1 != "_did_abort")
              .filter(_._1 != "_op_start")
              .filter(_._1 != "_op_end")
              .toArray
              .sortBy(_._1)
              .map((k, v) => s"$k=$v")
              .mkString(", ")
          end if
        }) [$operationStart,$operationEnd] pid=$pid"
    end descriptiveLabel
  end TraceOperation

  final class TraceRecord(val fingerprint: Long, val tlaValue: TLAValue)
      extends TraceOperation:
    override def hashCode(): Int =
      (this.getClass(), fingerprint).hashCode()

    override def equals(that: Any): Boolean =
      that match
        case that: TraceRecord => fingerprint == that.fingerprint
        case _                 => false
    end equals

    override def toString(): String = s"TraceRecord($fingerprint)"

    def action: TLAValue = tlaValue("__action")

    def shortId: String = shortIdFromFingerprint(fingerprint)

    def depth: Int =
      tlaValue("__pc").asMap.view.values
        .map(_.asInt - 1)
        .sum + 1 // for init
    end depth

    def depthStr: String = depth.toString()

    def depthOption: Option[Int] = Some(depth)

    def successorOperations: View[TLAValue] =
      tlaValue
        .get("__successors")
        .map(_.asMap.view)
        .map(_.values.view)
        .getOrElse(View.empty)
    end successorOperations

    def successorRecords: View[TraceRecord] =
      allSuccessors
        .get(fingerprint)
        .fold(View.empty)(_.view)
        .map(states)
    end successorRecords

    def predecessorRecords: View[TraceRecord] =
      allPredecessors
        .get(fingerprint)
        .fold(View.empty)(_.view)
        .map(states)
    end predecessorRecords

    def isStallState: Boolean =
      successorRecords
        .filter(_.fingerprint != fingerprint)
        .isEmpty
  end TraceRecord

  object TraceRecord:
    def byShortId(id: String): TraceRecord =
      states(fingerprintFromShortId(id))
  end TraceRecord

  final case class TraceOperationRaw(
      val action: TLAValue,
      override val pid: Int,
      idx: Int,
  ) extends TraceOperation:
    def tlaValue: TLAValue = action
    def shortId: String = ""
    def depthStr: String = s"?$pid+$idx"
    def depthOption = None
    def predecessorRecords: View[TraceRecord] = View.empty
  end TraceOperationRaw

  object TraceOperationRaw:
    def byCoordinates(pid: Int, idx: Int): Option[TraceOperationRaw] =
      traces
        .lift(pid)
        .flatMap(_.lift(idx))
        .map(_.transform(upack.Msg))
        .map: msg =>
          msg.obj
            .get(upack.Str("operation"))
            .foreach: op =>
              op.obj
                .get(upack.Str("_op_start"))
                .foreach: start =>
                  op.obj(upack.Str("_op_start")) =
                    upack.Int32(compressedTimestamps(start.int64))
                  msg.obj(upack.Str("_op_start_orig")) =
                    upack.Str(start.int64.toString())
              op.obj
                .get(upack.Str("_op_end"))
                .foreach: end =>
                  op.obj(upack.Str("_op_end")) =
                    upack.Int32(compressedTimestamps(end.int64))
                  msg.obj(upack.Str("_op_end_orig")) =
                    upack.Str(end.int64.toString())
          TraceOperationRaw(StateSpace.msgToTLA(msg), pid, idx)
    end byCoordinates
  end TraceOperationRaw
end StateSpace

object StateSpace:
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
end StateSpace
