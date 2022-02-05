package pgo.checker

import pgo.util.TLAExprInterpreter.TLAValue
import scala.collection.mutable

final case class VClock private (clock: Map[(String,TLAValue),Long]) {
  def apply(key: (String,TLAValue)): Long =
    clock.getOrElse(key, 0)

  def apply(archetypeName: String, self: TLAValue): Long =
    apply((archetypeName, self))

  def inc(archetypeName: String, self: TLAValue): VClock =
    inc((archetypeName, self))

  def inc(key: (String,TLAValue)): VClock =
    copy(clock = clock.updatedWith(key)(_.orElse(Some(0L)).map(_ + 1L)))

  def without(key: (String,TLAValue)): VClock =
    copy(clock = clock.removed(key))

  def <=<(other: VClock): Boolean =
    (this.clock.keysIterator ++ other.clock.keysIterator).forall { key =>
      this.clock.getOrElse(key, 0L) <= other.clock.getOrElse(key, 0L)
    }

  def <-<(other: VClock): Boolean =
    this <=< other &&
      (this.clock.keysIterator ++ other.clock.keysIterator).exists { key =>
        this.clock.getOrElse(key, 0L) < other.clock.getOrElse(key, 0L)
      }

  def concurrent(other: VClock): Boolean =
    !(this <-< other) && !(other <-< this)
}

object VClock {
  val origin: VClock = VClock(Map.empty)

  def fromJSON(v: ujson.Value): VClock =
    VClock(v.arr.view
      .map {
        case ujson.Arr(mutable.ArrayBuffer(ujson.Arr(mutable.ArrayBuffer(ujson.Str(archetypeName), self)), ujson.Num(idx))) =>
          (archetypeName, TLAValue.parseFromString(self.str)) -> idx.toLong
      }
      .toMap)
}
