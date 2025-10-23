---- MODULE ConcurrentQueueAPI ----
EXTENDS FiniteSets, Integers, Sequences, TLC

CONSTANTS Elements, MaxElements, Threads, MaxBulkSize

VARIABLES queue, enqueued, dequeued

vars == <<queue, enqueued, dequeued>>

TypeOK ==
    /\ queue \in Seq(Elements)
    /\ enqueued \in Nat
    /\ dequeued \in Nat
    \* /\ producerTokens \in SUBSET Threads
    \* /\ consumerTokens \in SUBSET Threads
    /\ dequeued <= enqueued

varsEnqueued == <<dequeued>>
varsDequeued == <<enqueued>>
varsEnqueueFail == <<queue, enqueued>>
varsDequeueFail == <<queue, dequeued>>
varsCreateProducer == <<queue, enqueued, dequeued>>
varsCreateConsumer == <<queue, enqueued, dequeued>>

QueueEnqueue(element, success) ==
    /\ element \in Elements
    /\ IF Len(queue) < MaxElements
       THEN /\ success = TRUE
            /\ queue' = queue \o <<element>>
            /\ enqueued' = enqueued + 1
       ELSE /\ success = FALSE
            /\ UNCHANGED varsEnqueueFail
    /\ UNCHANGED varsEnqueued

QueueEnqueueWithToken(prodToken, element, success) ==
    \* /\ prodToken \in producerTokens
    /\ element \in Elements
    /\ IF Len(queue) < MaxElements
       THEN /\ success = TRUE
            /\ queue' = queue \o <<element>>
            /\ enqueued' = enqueued + 1
       ELSE /\ success = FALSE
            /\ UNCHANGED varsEnqueueFail
    /\ UNCHANGED varsEnqueued

QueueEnqueueBulk(elements, count, success) ==
    /\ elements \in [1..MaxBulkSize -> Elements]
    /\ count \in 1..MaxBulkSize
    /\ Len(elements) >= count
    /\ IF Len(queue) + count <= MaxElements
       THEN /\ success = TRUE
            /\ queue' = queue \o SubSeq(elements, 1, count)
            /\ enqueued' = enqueued + count
       ELSE /\ success = FALSE
            /\ UNCHANGED varsEnqueueFail
    /\ UNCHANGED varsEnqueued

QueueEnqueueBulkWithToken(prodToken, elements, count, success) ==
    \* /\ prodToken \in producerTokens
    /\ elements \in [1..MaxBulkSize -> Elements]
    /\ count \in 1..MaxBulkSize
    /\ Len(elements) >= count
    /\ IF Len(queue) + count <= MaxElements
       THEN /\ success = TRUE
            /\ queue' = queue \o SubSeq(elements, 1, count)
            /\ enqueued' = enqueued + count
       ELSE /\ success = FALSE
            /\ UNCHANGED varsEnqueueFail
    /\ UNCHANGED varsEnqueued

QueueTryEnqueue(element, success) ==
    /\ element \in Elements
    /\ IF Len(queue) < MaxElements
       THEN /\ success = TRUE
            /\ queue' = queue \o <<element>>
            /\ enqueued' = enqueued + 1
       ELSE /\ success = FALSE
            /\ UNCHANGED varsEnqueueFail
    /\ UNCHANGED varsEnqueued

QueueTryEnqueueWithToken(prodToken, element, success) ==
    \* /\ prodToken \in producerTokens
    /\ element \in Elements
    /\ IF Len(queue) < MaxElements
       THEN /\ success = TRUE
            /\ queue' = queue \o <<element>>
            /\ enqueued' = enqueued + 1
       ELSE /\ success = FALSE
            /\ UNCHANGED varsEnqueueFail
    /\ UNCHANGED varsEnqueued

QueueTryEnqueueBulk(elements, count, success) ==
    /\ elements \in [1..MaxBulkSize -> Elements]
    /\ count \in 1..MaxBulkSize
    /\ Len(elements) >= count
    /\ IF Len(queue) + count <= MaxElements
       THEN /\ success = TRUE
            /\ queue' = queue \o SubSeq(elements, 1, count)
            /\ enqueued' = enqueued + count
       ELSE /\ success = FALSE
            /\ UNCHANGED varsEnqueueFail
    /\ UNCHANGED varsEnqueued

QueueTryEnqueueBulkWithToken(prodToken, elements, count, success) ==
    \* /\ prodToken \in producerTokens
    /\ elements \in [1..MaxBulkSize -> Elements]
    /\ count \in 1..MaxBulkSize
    /\ Len(elements) >= count
    /\ IF Len(queue) + count <= MaxElements
       THEN /\ success = TRUE
            /\ queue' = queue \o SubSeq(elements, 1, count)
            /\ enqueued' = enqueued + count
       ELSE /\ success = FALSE
            /\ UNCHANGED varsEnqueueFail
    /\ UNCHANGED varsEnqueued

QueueTryDequeue(element, success) ==
    /\ IF Len(queue) > 0
       THEN /\ success = TRUE
            /\ element = Head(queue)
            /\ queue' = Tail(queue)
            /\ dequeued' = dequeued + 1
       ELSE /\ success = FALSE
            /\ element \in Elements  
            /\ UNCHANGED varsDequeueFail
    /\ UNCHANGED varsDequeued

QueueTryDequeueWithToken(consToken, element, success) ==
    \* /\ consToken \in consumerTokens
    /\ IF Len(queue) > 0
       THEN /\ success = TRUE
            /\ element = Head(queue)
            /\ queue' = Tail(queue)
            /\ dequeued' = dequeued + 1
       ELSE /\ success = FALSE
            /\ element \in Elements  
            /\ UNCHANGED varsDequeueFail
    /\ UNCHANGED varsDequeued

QueueTryDequeueBulk(elements, max, count) ==
    /\ elements \in [1..MaxBulkSize -> Elements]
    /\ max \in 1..MaxBulkSize
    /\ Len(elements) >= max
    /\ LET actualCount == IF Len(queue) >= max THEN max ELSE Len(queue)
       IN /\ count = actualCount
          /\ IF actualCount > 0
             THEN /\ queue' = SubSeq(queue, actualCount + 1, Len(queue))
                  /\ dequeued' = dequeued + actualCount
             ELSE /\ UNCHANGED <<queue, dequeued>>
    /\ UNCHANGED varsDequeued

QueueTryDequeueBulkWithToken(consToken, elements, max, count) ==
    \* /\ consToken \in consumerTokens
    /\ elements \in [1..MaxBulkSize -> Elements]
    /\ max \in 1..MaxBulkSize
    /\ Len(elements) >= max
    /\ LET actualCount == IF Len(queue) >= max THEN max ELSE Len(queue)
       IN /\ count = actualCount
          /\ IF actualCount > 0
             THEN /\ queue' = SubSeq(queue, actualCount + 1, Len(queue))
                  /\ dequeued' = dequeued + actualCount
             ELSE /\ UNCHANGED <<queue, dequeued>>
    /\ UNCHANGED varsDequeued

QueueTryDequeueFromProducer(prodToken, element, success) ==
    \* /\ prodToken \in producerTokens
    /\ IF Len(queue) > 0
       THEN /\ success = TRUE
            /\ element = Head(queue)
            /\ queue' = Tail(queue)
            /\ dequeued' = dequeued + 1
       ELSE /\ success = FALSE
            /\ element \in Elements 
            /\ UNCHANGED varsDequeueFail
    /\ UNCHANGED varsDequeued

QueueTryDequeueBulkFromProducer(prodToken, elements, max, count) ==
    \* /\ prodToken \in producerTokens
    /\ elements \in [1..MaxBulkSize -> Elements]
    /\ max \in 1..MaxBulkSize
    /\ Len(elements) >= max
    /\ LET actualCount == IF Len(queue) >= max THEN max ELSE Len(queue)
       IN /\ count = actualCount
          /\ IF actualCount > 0
             THEN /\ queue' = SubSeq(queue, actualCount + 1, Len(queue))
                  /\ dequeued' = dequeued + actualCount
             ELSE /\ UNCHANGED <<queue, dequeued>>
    /\ UNCHANGED varsDequeued

QueueSizeApprox(size) ==
    /\ size = Len(queue)
    /\ UNCHANGED vars

\* CreateProducerToken(thread) ==
\*     /\ thread \in Threads
\*     /\ thread \notin producerTokens
\*     /\ producerTokens' = producerTokens \cup {thread}
\*     /\ UNCHANGED varsCreateProducer

\* CreateConsumerToken(thread) ==
\*     /\ thread \in Threads
\*     /\ thread \notin consumerTokens
\*     /\ consumerTokens' = consumerTokens \cup {thread}
\*     /\ UNCHANGED varsCreateConsumer

Init ==
    /\ queue = <<>>
    /\ enqueued = 0
    /\ dequeued = 0
    \* /\ producerTokens = Threads 
    \* /\ consumerTokens = Threads

Next ==
    \/ \E element \in Elements, success \in BOOLEAN :
        QueueEnqueue(element, success)
    \* \/ \E prodToken \in Threads, element \in Elements, success \in BOOLEAN :
    \*     QueueEnqueueWithToken(prodToken, element, success)
    \/ \E elements \in [1..MaxBulkSize -> Elements], count \in 1..MaxBulkSize, success \in BOOLEAN :
        QueueEnqueueBulk(elements, count, success)
    \* \/ \E prodToken \in Threads, elements \in [1..MaxBulkSize -> Elements], count \in 1..MaxBulkSize, success \in BOOLEAN :
    \*     QueueEnqueueBulkWithToken(prodToken, elements, count, success)
    \/ \E element \in Elements, success \in BOOLEAN :
        QueueTryEnqueue(element, success)
    \* \/ \E prodToken \in Threads, element \in Elements, success \in BOOLEAN :
    \*     QueueTryEnqueueWithToken(prodToken, element, success)
    \/ \E elements \in [1..MaxBulkSize -> Elements], count \in 1..MaxBulkSize, success \in BOOLEAN :
        QueueTryEnqueueBulk(elements, count, success)
    \* \/ \E prodToken \in Threads, elements \in [1..MaxBulkSize -> Elements], count \in 1..MaxBulkSize, success \in BOOLEAN :
    \*     QueueTryEnqueueBulkWithToken(prodToken, elements, count, success)
    \/ \E element \in Elements, success \in BOOLEAN :
        QueueTryDequeue(element, success)
    \* \/ \E consToken \in Threads, element \in Elements, success \in BOOLEAN :
    \*     QueueTryDequeueWithToken(consToken, element, success)
    \/ \E elements \in [1..MaxBulkSize -> Elements], max \in 1..MaxBulkSize, count \in 0..MaxBulkSize :
        QueueTryDequeueBulk(elements, max, count)
    \* \/ \E consToken \in Threads, elements \in [1..MaxBulkSize -> Elements], max \in 1..MaxBulkSize, count \in 0..MaxBulkSize :
    \*     QueueTryDequeueBulkWithToken(consToken, elements, max, count)
    \/ \E prodToken \in Threads, element \in Elements, success \in BOOLEAN :
        QueueTryDequeueFromProducer(prodToken, element, success)
    \* \/ \E prodToken \in Threads, elements \in [1..MaxBulkSize -> Elements], max \in 1..MaxBulkSize, count \in 0..MaxBulkSize :
    \*     QueueTryDequeueBulkFromProducer(prodToken, elements, max, count)
    \/ \E size \in 0..MaxElements :
        QueueSizeApprox(size)


QueueInvariant ==
    /\ Len(queue) = enqueued - dequeued
    /\ dequeued <= enqueued
    /\ enqueued <= MaxElements + dequeued

StateConstraints ==
    /\ Len(queue) <= 2
    /\ enqueued <= 4
    /\ dequeued <= 4

NoLostElements ==
    enqueued - dequeued = Len(queue)


Spec == Init /\ [][Next]_vars

====