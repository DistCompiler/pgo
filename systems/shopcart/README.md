# shopcart

shopcart models an AWORSET set CRDT.

For more information check out this report:
[Distributed State in PGo](https://shayanh.com/files/diststate.pdf).


## Model

We express query and update methods of CRDTs using mapping macros in MPCal. For
each CRDT, we define a mapping macro that its read section implements the query
method and its write section implements the update method. In this case, the
mapping macro is `AWORSet`.

According to the CRDT paper [Shapiro et al. 2011], every node infinitely often
sends its state to every other node. Each node after receiving another node’s
state, merges the received state into its local state. So there is no
restriction on the execution order of merge operations. To simulate this
behavior, we created a new process in the specification that runs concurrently
with node archetypes. This process, in each of its execution step, merges states
of two nodes that do not have equal states (merging states of two nodes with the
same state has no effect). The model checker will explore every possible
execution orders of running this process along with that of the node archetypes.
This allows us to make sure that a system works correctly in every possible way
that merge operations can happen. Note that for this, we do not use an
`archetype`, and we use a `process` because we wish to model-check this behavior
without compiling it into Go. The actual broadcasting in the Go implementation
is included in the CRDT resources.

### Properties

- Eventual Delivery: an update delivered at some node is eventually delivered to
  all nodes.
- Strong Convergence: Correct replicas that have delivered the same updates have
  equivalent state.
- Termination: All method executions terminate.