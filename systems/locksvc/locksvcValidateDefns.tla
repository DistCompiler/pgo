---- MODULE locksvcValidateDefns ----
EXTENDS Sequences

network_read(state, self, idx, value, next(_)) ==
    /\ state.network[idx] # <<>>
    /\ Head(state.network[idx]) = value
    /\ next([state EXCEPT !.network[idx] = Tail(@)])

network_write(state, self, idx, value, next(_)) ==
    next([state EXCEPT !.network[idx] = Append(@, value)])

hasLock_write(state, self, idx, value, next(_)) ==
    next([state EXCEPT !.hasLock[idx] = value])

====