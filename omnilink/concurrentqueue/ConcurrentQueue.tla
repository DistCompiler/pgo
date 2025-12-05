---- MODULE ConcurrentQueue ----
EXTENDS Integers, Sequences, SequencesExt, FiniteSets, FiniteSetsExt, TLC

CONSTANTS Elements, Producers, Consumers

VARIABLES queues, enqueueInProgress, dequeueInProgress, sizeApproxMax

vars == <<queues, enqueueInProgress, dequeueInProgress, sizeApproxMax>>

QueueSize ==
    FoldFunction(LAMBDA elem, acc : Len(elem) + acc, 0, queues)

SizeApproxMax ==
    FoldFunction(+, 0, sizeApproxMax)

TypeOK ==
    /\ queues \in [Producers -> Seq(Elements)]
    /\ enqueueInProgress \in [Producers -> Seq(Elements)]
    /\ dequeueInProgress \in [Consumers -> Seq(Elements)]
    /\ sizeApproxMax \in [Producers -> Nat]

RecordDequeue(elem) == TRUE
RecordNoDequeue == TRUE

\* Note: Enqueue with no token uses an implicit thread-local producer token.
\* Therefore, it is just modeled as EnqueueWithToken and a specific
\* producer parameter.

EnqueueWithToken_Step(producer, elements) ==
    /\ IsStrictPrefix(enqueueInProgress[producer], elements)
    /\ LET elem ==
            IF   enqueueInProgress[producer] = <<>>
            THEN Head(elements)
            ELSE elements[Len(enqueueInProgress[producer]) + 1]
       IN  /\ enqueueInProgress' = [enqueueInProgress EXCEPT ![producer] = Append(@, elem)]
           /\ queues' = [queues EXCEPT ![producer] = Append(@, elem)]
           /\ sizeApproxMax' = [sizeApproxMax EXCEPT ![producer] = Max({@, Len(queues'[producer])})]
           /\ RecordNoDequeue
           /\ UNCHANGED dequeueInProgress

EnqueueWithToken_Done(producer, elements) ==
    /\ enqueueInProgress[producer] = elements
    /\ enqueueInProgress' = [enqueueInProgress EXCEPT ![producer] = <<>>]
    /\ RecordNoDequeue
    /\ UNCHANGED <<queues, dequeueInProgress, sizeApproxMax>>

DequeueWithToken_Step(consumer, producer, elements) ==
    /\ IsStrictPrefix(dequeueInProgress[consumer], elements)
    /\ LET elem ==
            IF   dequeueInProgress[consumer] = <<>>
            THEN Head(elements)
            ELSE elements[Len(dequeueInProgress[consumer]) + 1]
       IN  /\ IsPrefix(<<elem>>, queues[producer])
           /\ dequeueInProgress' = [dequeueInProgress EXCEPT ![consumer] = Append(@, elem)]
           /\ queues' = [queues EXCEPT ![producer] = Tail(@)]
           /\ RecordDequeue(elem)
           /\ UNCHANGED <<enqueueInProgress, sizeApproxMax>>

DequeueWithToken_Done(consumer, producer, elements) ==
    /\ dequeueInProgress[consumer] = elements
    /\ dequeueInProgress' = [dequeueInProgress EXCEPT ![consumer] = <<>>]
    /\ RecordNoDequeue
    /\ UNCHANGED <<queues, enqueueInProgress, sizeApproxMax>>

Dequeue_Step(consumer, elements) ==
    \E producer \in Producers :
        DequeueWithToken_Step(consumer, producer, elements)

Dequeue_Done(consumer, elements) ==
    /\ dequeueInProgress[consumer] = elements
    /\ dequeueInProgress' = [dequeueInProgress EXCEPT ![consumer] = <<>>]
    /\ RecordNoDequeue
    /\ UNCHANGED <<queues, enqueueInProgress, sizeApproxMax>>

SizeApprox(size) ==
    /\ size <= SizeApproxMax
    /\ RecordNoDequeue
    /\ UNCHANGED vars

CONSTANT BulkSize
ASSUME BulkSize >= 1

Init ==
    /\ queues = [producer \in Producers |-> <<>>]
    /\ enqueueInProgress = [producer \in Producers |-> <<>>]
    /\ dequeueInProgress = [consumer \in Consumers |-> <<>>]
    /\ sizeApproxMax = [producer \in Producers |-> 0]

Next ==
    \/ \E producer \in Producers, elements \in SeqOf(Elements, BulkSize) :
        \/ EnqueueWithToken_Step(producer, elements)
        \/ EnqueueWithToken_Done(producer, elements)
    \/ \E consumer \in Consumers, elements \in SeqOf(Elements, BulkSize) :
        \/ Dequeue_Step(consumer, elements)
        \/ Dequeue_Done(consumer, elements)
    \/ \E consumer \in Consumers, producer \in Producers, elements \in SeqOf(Elements, BulkSize) :
        \/ DequeueWithToken_Step(consumer, producer, elements)
        \/ DequeueWithToken_Done(consumer, producer, elements)
    \/ \E size \in 0 .. SizeApproxMax :
        SizeApprox(size)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ SF_vars(
        \E consumer \in Consumers, elements \in SeqOf(Elements, BulkSize) :
            Dequeue_Step(consumer, elements)
       )
    /\ SF_vars(
        \E consumer \in Consumers, producer \in Producers, elements \in SeqOf(Elements, BulkSize) :
            DequeueWithToken_Step(consumer, producer, elements)
       )

====