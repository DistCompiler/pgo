---- MODULE MCConcurrentQueue ----
EXTENDS ConcurrentQueue

StateConstraints ==
    /\ QueueSize <= 4

SizeApproxMaxRange ==
    \A producer \in Producers :
        Len(queues[producer]) <= sizeApproxMax[producer]

====