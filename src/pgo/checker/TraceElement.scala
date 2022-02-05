package pgo.checker

import pgo.util.CriticalSectionInterpreter.CSElement
import pgo.util.TLAExprInterpreter.TLAValue

final case class TraceElement(archetypeName: String, self: TLAValue, elements: List[CSElement], clock: VClock) {
  def clockKey: (String,TLAValue) = (archetypeName, self)
  def index: Long = clock(clockKey)
}

object TraceElement {
  def fromJSON(v: ujson.Value): TraceElement =
    TraceElement(
      archetypeName = v("archetypeName").str,
      self = TLAValue.parseFromString(v("self").str),
      elements =
        v("csElements").arr.iterator
          .map(CSElement.fromJSON)
          .toList,
      clock = VClock.fromJSON(v("clock")))
}
