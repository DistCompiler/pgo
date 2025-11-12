---- MODULE ConcurrentQueue ----
EXTENDS Integers, Sequences, SequencesExt, FiniteSets, FiniteSetsExt

CONSTANTS Elements, Producers

VARIABLES queues, sizeApproxMax

vars == <<queues, sizeApproxMax>>

QueueSize ==
    FoldFunction(LAMBDA elem, acc : Len(elem) + acc, 0, queues)

SizeApproxMax ==
    FoldFunction(+, 0, sizeApproxMax)

TypeOK ==
    /\ queues \in [Producers -> Seq(Elements)]
    /\ sizeApproxMax \in [Producers -> Nat]

\* Note: Enqueue with no token uses an implicit thread-local producer token.
\* Therefore, it is just modeled as EnqueueWithToken and a specific
\* producer parameter.

EnqueueWithToken(producer, elements) ==
    /\ queues' = [queues EXCEPT ![producer] = @ \o elements]
    /\ sizeApproxMax' = [sizeApproxMax EXCEPT ![producer] = Max({@, Len(queues'[producer])})]

DequeueWithToken(producer, elements) ==
    /\ IsPrefix(elements, queues[producer])
    /\ queues' = [queues EXCEPT ![producer] =
        IF   Len(@) = Len(elements)
        THEN <<>>
        ELSE SubSeq(@, Len(elements) + 1, Len(@))
       ]
    /\ UNCHANGED sizeApproxMax

\* TODO: let PGo parse local RECURSIVE trampolines
RECURSIVE DequeueImpl(_, _)
DequeueImpl(_elements, _queues) ==
    \/ /\ _elements = <<>>
       /\ queues' = _queues
    \/ \E producer \in Producers :
        \E pfx \in CommonPrefixes({ _elements, _queues[producer] }) :
            LET _queues2 == [_queues EXCEPT ![producer] =
                    IF   Len(@) = Len(pfx)
                    THEN <<>>
                    ELSE SubSeq(@, Len(pfx) + 1, Len(@))]
            IN  /\ pfx # <<>>
                /\ IF   Len(_elements) = Len(pfx)
                   THEN queues' = _queues2
                   ELSE DequeueImpl(
                            SubSeq(_elements, Len(pfx) + 1, Len(_elements)),
                            _queues2
                        )

Dequeue(elements) ==
    \* Non-token dequeue may drain multiple queues in some order,
    \* but it will always dequeue in order wrt. the same producer.
    /\ DequeueImpl(elements, queues)
    /\ UNCHANGED sizeApproxMax

SizeApprox(size) ==
    /\ size <= SizeApproxMax
    /\ UNCHANGED vars

CONSTANT BulkSize
ASSUME BulkSize >= 1

Init ==
    /\ queues = [producer \in Producers |-> <<>>]
    /\ sizeApproxMax = [producer \in Producers |-> 0]

Next ==
    \/ \E producer \in Producers, elements \in SeqOf(Elements, BulkSize) :
        EnqueueWithToken(producer, elements)
    \/ \E elements \in SeqOf(Elements, BulkSize) :
        Dequeue(elements)
    \/ \E producer \in Producers, elements \in SeqOf(Elements, BulkSize) :
        DequeueWithToken(producer, elements)
    \/ \E size \in 0 .. SizeApproxMax :
        SizeApprox(size)

Spec == Init /\ [][Next]_vars

====