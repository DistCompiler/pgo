package pgo.checker

import CriticalSectionInterpreter.CSElement
import pgo.util.Description
import pgo.util.TLAExprInterpreter.TLAValue

import Description._

final case class TraceElement(archetypeName: String, self: TLAValue, elements: List[CSElement], clock: VClock) {
  def clockKey: (String,TLAValue) = (archetypeName, self)
  def index: Long = clock(clockKey)

  def describe: Description =
    d"trace element at $archetypeName(${self.describe}) with ${
      clock.describe
    }\nand ${
      if(elements.isEmpty) {
        d"no known operations"
      } else {
        d"operations" +
          elements.view
            .map(_.describe.ensureLineBreakBefore)
            .flattenDescriptions
            .indented
      }
    }"
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
