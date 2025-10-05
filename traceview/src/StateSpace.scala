package pgo.traceview

import scala.collection.View

import pgo.util.TLAExprInterpreter.{TLAValue, TLAValueTuple}

final class StateSpace(val tlaValue: TLAValue):
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
      .map((fingerprint, id) => (fingerprint, id.padTo(maxWidth, '0')))
      .toMap
  end shortIdFromFingerprint

  private val fingerprintFromShortId: Map[String, Long] =
    shortIdFromFingerprint.map(_.reverse)

  private val shortTimestamps: Map[Int, Int] =
    states.view.values
      .flatMap(state => List(state.operationStart, state.operationEnd))
      .toArray
      .sortInPlace
      .view
      .zipWithIndex
      .map((ts, idx) => (ts, idx + 1))
      .toMap
  end shortTimestamps

  def deepestStalledStates: List[TraceRecord] =
    val maxDepth = states.view.values.map(_.depth).max
    states.view.values
      .filter(_.depth == maxDepth)
      .toList
  end deepestStalledStates

  final class TraceRecord(val fingerprint: Long, val tlaValue: TLAValue):
    override def hashCode(): Int =
      (classOf[TraceRecord], fingerprint).hashCode()

    override def equals(that: Any): Boolean =
      that match
        case that: TraceRecord => fingerprint == that.fingerprint
        case _                 => false
    end equals

    def action: TLAValue = tlaValue("__action")

    def shortId: String = shortIdFromFingerprint(fingerprint)

    def operationName: String =
      action.get("operation_name").fold("<init>")(_.asString)
    def operationStart: Int = action.get("op_start").fold(0)(_.asInt)
    def operationStartShort: Int = shortTimestamps(operationStart)
    def operationEnd: Int = action.get("op_end").fold(0)(_.asInt)
    def operationEndShort: Int = shortTimestamps(operationEnd)
    def pid: Int = action.get("pid").fold(-1)(_.asInt)

    def depth: Int =
      tlaValue("__pc").asMap.view.values
        .map(_.asInt - 1)
        .sum - 1
    end depth

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

    def isInitialState: Boolean =
      action == TLAValueTuple(Vector.empty)
    end isInitialState

    def isStallState: Boolean =
      successorRecords
        .filter(_.fingerprint != fingerprint)
        .isEmpty

    def titleString: String =
      if isInitialState
      then "initial state"
      else s"$operationName: pid=$pid, span=[$operationStart, $operationEnd]"
    end titleString

    def descriptiveLabel: String =
      val didAbortPart =
        if action.get("operation").fold(false)(_.apply("_did_abort").asBoolean)
        then "!!"
        else ""
      s"$shortId $didAbortPart$operationName(${
          if action == TLAValueTuple(Vector())
          then ""
          else
            action
              .get("operation")
              .map: op =>
                op.asMap.view
                  .map: (k, v) =>
                    val vStr = v.toString
                    val truncVStr =
                      if vStr.size > 25
                      then s"${vStr.take(25)}.."
                      else vStr
                    (k.asString, truncVStr)
                  .filter(_._1 != "_meta")
                  .filter(_._1 != "_did_abort")
                  .toArray
                  .sortBy(_._1)
                  .map((k, v) => s"$k=$v")
                  .mkString(", ")
              .getOrElse("")
          end if
        }) [$operationStartShort,$operationEndShort] pid=$pid"
    end descriptiveLabel
  end TraceRecord

  object TraceRecord:
    def byShortId(id: String): TraceRecord =
      states(fingerprintFromShortId(id))
  end TraceRecord
end StateSpace

object StateSpace:
  def fromFile(path: os.Path): StateSpace =
    StateSpace(TLAValue.parseFromTLCBinFmtGZIP(os.read.stream(path)))
end StateSpace
