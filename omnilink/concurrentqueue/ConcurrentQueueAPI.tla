---- MODULE ConcurrentQueueAPI ----
EXTENDS FiniteSets, Integers, Sequences, TLC, SequencesExt, FiniteSetsExt

CONSTANTS Elements, MaxElements, Threads, MaxBulkSize

VARIABLES queues, enqueued, dequeued

vars == <<queues, enqueued, dequeued>>

QueueOf(thread) == queues[thread]
UpdateQueue(thread, seq) == [queues EXCEPT ![thread] = seq]

RECURSIVE TotalLenHelper(_, _)

TotalLenHelper(qs, ts) ==
    IF ts = {}
    THEN 0
    ELSE LET t == CHOOSE x \in ts : TRUE
         IN Len(qs[t]) + TotalLenHelper(qs, ts \ {t})

TotalLen(qs) == TotalLenHelper(qs, Threads)

CanEnqueue(count) == TotalLen(queues) + count <= MaxElements
CanDequeue(thread) == Len(QueueOf(thread)) > 0

Take(seq, n) ==
    IF n <= 0
    THEN << >>
    ELSE IF n >= Len(seq)
         THEN seq
         ELSE SubSeq(seq, 1, n)

MinCount(a, b) ==
    IF a <= b THEN a ELSE b

PayloadForElement(element) == <<element>>

BulkBufferSet == { seq \in Seq(Elements) : Len(seq) <= MaxBulkSize }
BulkBuffer(elements) == elements \in BulkBufferSet
BulkPayload(elements, count) == Take(elements, count)

BulkArgsOk(elements, count) ==
    /\ BulkBuffer(elements)
    /\ count \in 1..MaxBulkSize
    /\ Len(elements) >= count
    /\ IsPrefix(BulkPayload(elements, count), elements)

EnqueueOutcome(canEnqueue, thread, payload, delta, success) ==
    IF canEnqueue
    THEN /\ success = TRUE
         /\ queues' = UpdateQueue(thread, QueueOf(thread) \o payload)
         /\ enqueued' = enqueued + delta
    ELSE /\ success = FALSE
         /\ UNCHANGED queues
         /\ UNCHANGED enqueued

DequeueOutcome(canDequeue, thread, element, success) ==
    IF canDequeue
    THEN /\ success = TRUE
         /\ element = Head(QueueOf(thread))
         /\ queues' = UpdateQueue(thread, Tail(QueueOf(thread)))
         /\ dequeued' = dequeued + 1
    ELSE /\ success = FALSE
         /\ element \in Elements
         /\ UNCHANGED queues
         /\ UNCHANGED dequeued

BulkActualCount(thread, max) == MinCount(Len(QueueOf(thread)), max)

BulkDequeueOutcome(thread, payload) ==
    LET actualCount == Len(payload)
    IN IF actualCount > 0
       THEN /\ \A i \in 1..actualCount : payload[i] = QueueOf(thread)[i]
            /\ queues' = UpdateQueue(thread, SubSeq(QueueOf(thread), actualCount + 1, Len(QueueOf(thread))))
            /\ dequeued' = dequeued + actualCount
       ELSE /\ UNCHANGED queues
            /\ UNCHANGED dequeued

TypeOK ==
    /\ queues \in [Threads -> Seq(Elements)]
    /\ enqueued \in Nat
    /\ dequeued \in Nat
    /\ dequeued <= enqueued

QueueEnqueue(element, success, thread) ==
    /\ thread \in Threads
    /\ element \in Elements
    /\ EnqueueOutcome(CanEnqueue(1), thread, PayloadForElement(element), 1, success)
    /\ UNCHANGED dequeued

QueueEnqueueWithToken(prodToken, element, success, thread) ==
    \* /\ prodToken \in Threads
    /\ QueueEnqueue(element, success, thread)

QueueEnqueueBulk(elements, count, success, thread) ==
    /\ thread \in Threads
    /\ BulkArgsOk(elements, count)
    /\ LET payload == BulkPayload(elements, count)
       IN EnqueueOutcome(CanEnqueue(count), thread, payload, count, success)
    /\ UNCHANGED dequeued

QueueEnqueueBulkWithToken(prodToken, elements, count, success, thread) ==
    \* /\ prodToken \in Threads
    /\ QueueEnqueueBulk(elements, count, success, thread)

QueueTryEnqueue(element, success, thread) ==
    /\ QueueEnqueue(element, success, thread)

QueueTryEnqueueWithToken(prodToken, element, success, thread) ==
    /\ QueueEnqueue(element, success, thread)

QueueTryEnqueueBulk(elements, count, success, thread) ==
    /\ QueueEnqueueBulk(elements, count, success, thread)

QueueTryEnqueueBulkWithToken(prodToken, elements, count, success, thread) ==
    /\ QueueEnqueueBulk(elements, count, success, thread)

QueueTryDequeue(element, success, thread) ==
    /\ thread \in Threads
    /\ DequeueOutcome(CanDequeue(thread), thread, element, success)
    /\ UNCHANGED enqueued

QueueTryDequeueWithToken(consToken, element, success, thread) ==
    \* /\ consToken \in Threads
    /\ QueueTryDequeue(element, success, thread)

QueueTryDequeueBulk(elements, max, count, thread) ==
    /\ thread \in Threads
    /\ BulkBuffer(elements)
    /\ max \in 1..MaxBulkSize
    /\ LET actualCount == BulkActualCount(thread, max)
           payload == BulkPayload(elements, actualCount)
       IN /\ count = actualCount
          /\ BulkDequeueOutcome(thread, payload)
    /\ UNCHANGED enqueued

QueueTryDequeueBulkWithToken(consToken, elements, max, count, thread) ==
    \* /\ consToken \in Threads
    /\ QueueTryDequeueBulk(elements, max, count, thread)

QueueTryDequeueFromProducer(prodToken, element, success, thread) ==
    \* /\ prodToken \in Threads
    /\ QueueTryDequeue(element, success, thread)

QueueTryDequeueBulkFromProducer(prodToken, elements, max, count, thread) ==
    \* /\ prodToken \in Threads
    /\ QueueTryDequeueBulk(elements, max, count, thread)

QueueSizeApprox(size) ==
    /\ size = TotalLen(queues)
    /\ UNCHANGED queues
    /\ UNCHANGED enqueued
    /\ UNCHANGED dequeued

Init ==
    /\ queues = [thread \in Threads |-> <<>>]
    /\ enqueued = 0
    /\ dequeued = 0

Next ==
    \/ \E thread \in Threads, element \in Elements, success \in BOOLEAN :
        QueueEnqueue(element, success, thread)
    \/ \E thread \in Threads, elements \in BulkBufferSet, count \in 1..MaxBulkSize, success \in BOOLEAN :
        QueueEnqueueBulk(elements, count, success, thread)
    \/ \E thread \in Threads, element \in Elements, success \in BOOLEAN :
        QueueTryEnqueue(element, success, thread)
    \/ \E thread \in Threads, elements \in BulkBufferSet, count \in 1..MaxBulkSize, success \in BOOLEAN :
        QueueTryEnqueueBulk(elements, count, success, thread)
    \* \/ \E thread \in Threads, element \in Elements, success \in BOOLEAN :
    \*     QueueTryDequeue(element, success, thread)
    \* \/ \E thread \in Threads, elements \in BulkBufferSet, max \in 1..MaxBulkSize, count \in 0..MaxBulkSize :
    \*     QueueTryDequeueBulk(elements, max, count, thread)
    \* \/ \E thread \in Threads, element \in Elements, success \in BOOLEAN :
    \*     QueueTryDequeueFromProducer(thread, element, success, thread)
    \* \/ \E thread \in Threads, elements \in BulkBufferSet, max \in 1..MaxBulkSize, count \in 0..MaxBulkSize :
    \*     QueueTryDequeueBulkFromProducer(thread, elements, max, count, thread)
    \/ \E size \in 0..MaxElements :
        QueueSizeApprox(size)

NoLostElements ==
    enqueued - dequeued = TotalLen(queues)

QueueInvariant ==
    /\ NoLostElements
    /\ enqueued <= MaxElements + dequeued

StateConstraints ==
    /\ TotalLen(queues) <= 2
    /\ enqueued <= 4
    /\ dequeued <= 4

Spec == Init /\ [][Next]_vars

====