package pgo.checker

import pgo.util.TLAExprInterpreter.TLAValue
import pgo.util.!!!

import scala.collection.mutable

private final class TraceConsumer {
  private val clockKeysSeen = mutable.HashSet.empty[(String,TLAValue)]
  private val clockKeysSeenOrd = mutable.ArrayBuffer.empty[(String,TLAValue)]

  private val historyPerNode = mutable.HashMap.empty[(String,TLAValue),TraceConsumer.NodeHistory]
  private def historyOf(clockKey: (String,TLAValue)): TraceConsumer.NodeHistory =
    historyPerNode.getOrElseUpdate(clockKey, TraceConsumer.NodeHistory.empty(clockKey))

  def consumeTraceElement(element: TraceElement): Unit = {
    if(!clockKeysSeen(element.clockKey)) {
      clockKeysSeen += element.clockKey
      clockKeysSeenOrd += element.clockKey
    }

    val history = historyOf(element.clockKey)
    history.pushElement(element)
  }

  final implicit class ElementIterableOnceOps(elementIterableOnce: IterableOnce[TraceElement]) {
    def findMinSet: List[TraceElement] =
      elementIterableOnce
        .iterator
        .foldLeft(mutable.ListBuffer.empty[TraceElement]) { (buf, element) =>
          // keep only elements that do not happen after the given element
          buf.filterInPlace(candidate => !(element.clock <-< candidate.clock))
          // only add the element if it does not happen after an already-present element
          if(!buf.exists(_.clock <-< element.clock)) {
            buf += element
          }
          // consequence: buf will contain only concurrent elements which come earliest out of the original set,
          //              or the single earliest element, or nothing at all if the input iterator was empty
          buf
        }
        .toList

    def findMaxSet: List[TraceElement] =
      elementIterableOnce
        .iterator
        .foldLeft(mutable.ListBuffer.empty[TraceElement]) { (buf, element) =>
          // same logic as min but backwards
          buf.filterInPlace(candidate => !(candidate.clock <-< element.clock))
          if(!buf.exists(element.clock <-< _.clock)) {
            buf += element
          }
          buf
        }
        .toList
  }

  def iterateElementsSafeOrder: Iterator[TraceElement] = {
    var reachedClock = VClock.origin
    var goalClock = VClock.origin
    val maxClock = clockKeysSeenOrd.view
      .foldLeft(VClock.origin) { (acc, clockKey) =>
        acc max historyOf(clockKey).lastElement.clock
      }

    Iterator.continually {
      clockKeysSeenOrd.iterator
        .filter(clockKey => reachedClock(clockKey) < goalClock(clockKey))
        .map(clockKey => historyOf(clockKey).at(reachedClock(clockKey) + 1).get)
        .findMinSet
        .headOption
        .orElse {
          // in this case, we have an entirely distinct clique to explore
          assert(reachedClock == goalClock)
          clockKeysSeenOrd.iterator
            .filter(clockKey => goalClock(clockKey) < maxClock(clockKey))
            .map(clockKey => historyOf(clockKey).at(reachedClock(clockKey) + 1).get)
            .findMinSet
            .headOption
        }
        .map { traceElement =>
          reachedClock = reachedClock.inc(traceElement.clockKey)
          goalClock = goalClock max traceElement.clock
          traceElement
        }
        .get
    }
      .takeWhile(_ => goalClock != maxClock)
  }

  implicit class TraceElementOps(traceElement: TraceElement) {
    def nextOpt: Option[TraceElement] =
      historyOf(traceElement.clockKey).at(traceElement.index + 1)

    def prevOpt: Option[TraceElement] =
      historyOf(traceElement.clockKey).at(traceElement.index - 1)

    def predecessors: List[TraceElement] =
      clockKeysSeenOrd.iterator
        .flatMap {
          case clockKey if clockKey == traceElement.clockKey =>
            historyOf(clockKey).at(traceElement.clock(clockKey) - 1)
          case clockKey =>
            historyOf(clockKey).at(traceElement.clock(clockKey))
        }
        .findMaxSet

    def successors: List[TraceElement] =
      clockKeysSeenOrd.iterator
        .flatMap { clockKey =>
          historyOf(clockKey).at(traceElement.clock(clockKey) + 1)
        }
        .findMinSet

    def possiblePredecessors: Iterator[TraceElement] =
      traceElement.prevOpt.iterator ++ // include direct predecessor of current element
        clockKeysSeenOrd.iterator
          .filter(_ != traceElement.clockKey)
          .flatMap { clockKey =>
            val startingPoint =
              if(traceElement.clock(clockKey) == 0) {
                historyOf(clockKey).at(1)
              } else {
                historyOf(clockKey).at(traceElement.clock(clockKey))
              }

            def forwards(traceElement: TraceElement): Iterator[TraceElement] =
              Iterator.single(traceElement) ++
                Iterator.unfold(traceElement) { traceElement =>
                  historyOf(clockKey).at(traceElement.clock(clockKey) + 1)
                    .map(traceElement => (traceElement, traceElement))
                }

            def backwards(traceElement: TraceElement): Iterator[TraceElement] =
              Iterator.single(traceElement) ++
                Iterator.unfold(traceElement) { traceElement =>
                  historyOf(clockKey).at(traceElement.clock(clockKey) - 1)
                    .map(traceElement => (traceElement, traceElement))
                }

            startingPoint.iterator
              .flatMap { startingPoint =>
                startingPoint.nextOpt.iterator
                  .flatMap(forwards(_).takeWhile(_.clock concurrent traceElement.clock)) ++
                  locally {
                    val (definitely, remaining) = backwards(startingPoint).span(_.clock concurrent traceElement.clock)
                    definitely ++ remaining.nextOption().filter(_.clock <-< traceElement.clock)
                  }
              }
          }
  }
}

private object TraceConsumer {
  private class NodeHistory private (clockKey: (String,TLAValue)) {
    private val data = mutable.LongMap.empty[TraceElement]
    private val keySet = mutable.SortedSet.empty[Long]

    def firstElement: TraceElement =
      data(keySet.firstKey)

    def lastElement: TraceElement =
      data(keySet.lastKey)

    def at(index: Long): Option[TraceElement] =
      data.get(index)

    def pushElement(element: TraceElement): Unit = {
      assert(element.clockKey == clockKey)
      val index = element.clock(element.clockKey)
      data.get(element.clock(element.clockKey)) match {
        case None =>
          keySet += element.index
          data(index) = element
        case Some(_) =>
          !!!
      }
    }
  }

  private object NodeHistory {
    def empty(clockKey: (String,TLAValue)): NodeHistory =
      new NodeHistory(clockKey = clockKey)
  }
}
