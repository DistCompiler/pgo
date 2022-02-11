package pgo.checker

import pgo.util.ById
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

  def iterateImmediateSuccessorPairs: Iterator[(TraceElement,TraceElement)] = {
    val visitedElements = mutable.HashSet.empty[ById[TraceElement]]
    final implicit class ElementIteratorOps(elementIterator: Iterator[TraceElement]) {
      def findMinSet: List[TraceElement] =
        elementIterator
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
    }

    def navigateImmediateSuccessorPairs(element: TraceElement): Iterator[(TraceElement,TraceElement)] =
      if(visitedElements.add(ById(element))) {
        val minSet = clockKeysSeenOrd.iterator
          .flatMap { clockKey =>
            historyOf(clockKey).at(element.clock(clockKey) + 1)
          }
          .findMinSet

        // avoiding flatMap, because this forces the overall iterator to be a tree of ++, which has a stackless optimisation
        minSet.iterator.map(element -> _) ++
          minSet.foldLeft(Iterator.empty[(TraceElement,TraceElement)]) { (acc, successor) =>
            acc ++ navigateImmediateSuccessorPairs(successor)
          }
      } else {
        Iterator.empty
      }

    clockKeysSeenOrd.iterator
      .map(historyOf)
      .map(_.firstElement)
      .findMinSet
      .iterator
      .flatMap(navigateImmediateSuccessorPairs)
      // not necessary, but for sanity
      .tapEach { case (before, after) => assert((before.clock <-< after.clock) || (before.clock concurrent after.clock)) }
  }

//  def iterateValidSequentialPairs: Iterator[(TraceElement,TraceElement)] = {
//    val visitedWavefronts = mutable.HashSet.empty[VClock]
//
//    def navigateSuccessors(wavefronts: Iterator[VClock]): Iterator[(TraceElement,TraceElement)] = {
//      val nextStream = wavefronts
//        .flatMap { wavefront =>
//          clockKeysSeenOrd.iterator
//            .flatMap { clockKey =>
//              val selfHistory = historyOf(clockKey)
//              val nextWavefront = wavefront.inc(clockKey)
//              if(visitedWavefronts(nextWavefront)) {
//                None
//              } else {
//                visitedWavefronts += nextWavefront
//                selfHistory.at(nextWavefront(clockKey)) match {
//                  case Some(after) =>
//                    // include the peers who have _the exact same_ clock, current key excepted.
//                    // that would mean this next element could have happened directly after the peer's element
//                    // ... and it also handles the +1 case, because that one is guaranteed to have this property
//                    val pairs = clockKeysSeenOrd.iterator
//                      .flatMap { peerKey =>
//                        historyOf(peerKey).at(wavefront(peerKey))
//                          .filter(_.clock.without(clockKey) == after.clock.without(clockKey))
//                          .map(_ -> after)
//                      }
//                    Some((nextWavefront, pairs))
//                  case None =>
//                    None
//                }
//              }
//            }
//        }
//
//      val (nextStream1, nextStream2) = nextStream.duplicate
//      nextStream1.flatMap(_._2) ++ navigateSuccessors(nextStream2.map(_._1))
//    }
//
//    navigateSuccessors(clockKeysSeenOrd.iterator.map(key => historyOf(key).firstElement.clock))
//      .distinctBy { case (before, after) => (ById(before), ById(after)) }
//  }
}

private object TraceConsumer {
  private class NodeHistory private (clockKey: (String,TLAValue)) {
    private val data = mutable.LongMap.empty[TraceElement]
    private val keySet = mutable.SortedSet.empty[Long]

    def firstElement: TraceElement =
      data(keySet.firstKey)

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
