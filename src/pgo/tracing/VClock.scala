package pgo.tracing

import pgo.util.TLAExprInterpreter.TLAValue
import scala.collection.mutable
import pgo.util.TLAExprInterpreter.TLAValueFunction
import pgo.util.TLAExprInterpreter.TLAValueNumber

final class VClock(val indices: Map[TLAValue, Long]):
  def toTLAValue: TLAValue =
    TLAValueFunction:
      indices.view
        .mapValues(clk => TLAValueNumber(clk.toInt))
        .toMap

  def merge(other: VClock): VClock =
    VClock:
      (indices.keysIterator ++ other.indices.keysIterator)
        .map: key =>
          key -> (indices
            .getOrElse(key, 0L) `max` other.indices.getOrElse(key, 0L))
        .toMap
end VClock

object VClock:
  def fromJSON(json: ujson.Value): VClock =
    VClock:
      json.arr.iterator
        .map:
          case ujson.Arr(
                mutable.ArrayBuffer(
                  ujson.Arr(mutable.ArrayBuffer(_, ujson.Str(self))),
                  ujson.Num(clk),
                ),
              ) =>
            TLAValue.parseFromString(self) -> clk.toLong
          case _ => ???
        .toMap
end VClock
