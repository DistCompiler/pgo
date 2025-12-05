---- MODULE MCConcurrentQueue ----
EXTENDS ConcurrentQueue, TLC

OrigCQ == INSTANCE ConcurrentQueue

VARIABLE dequeueHistory

varsImpl == <<queues, enqueueInProgress, dequeueInProgress, sizeApproxMax, dequeueHistory>>

InitImpl ==
    /\ OrigCQ!Init
    /\ dequeueHistory = <<>>

RecordDequeueImpl(elem) ==
    dequeueHistory' = Append(dequeueHistory, elem)

RecordNoDequeueImpl ==
    UNCHANGED dequeueHistory

StateConstraints ==
    /\ QueueSize <= 3
    /\ Len(dequeueHistory) <= 4

StateSymmetry ==
    Permutations(Producers)
    \cup Permutations(Consumers)
    \cup Permutations(Elements)

SizeApproxMaxRange ==
    \A producer \in Producers :
        Len(queues[producer]) <= sizeApproxMax[producer]

AllQueuesEventuallyEmpty ==
    \A producer \in Producers, elem \in Elements :
        (queues[producer] # <<>> /\ Last(queues[producer]) = elem)
            => <>(dequeueHistory # <<>> /\ Last(dequeueHistory) = elem)

====