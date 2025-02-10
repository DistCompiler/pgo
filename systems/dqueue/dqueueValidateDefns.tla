---- MODULE dqueueValidateDefns ----
EXTENDS Sequences, Integers

CONSTANT BUFFER_SIZE

network_read(state, self, idx, value, __rest(_)) ==
    /\ state.network[idx] # <<>>
    /\ Head(state.network[idx]) = value
    /\ __rest([state EXCEPT !.network[idx] = Tail(@)])

network_write(state, self, idx, value, __rest(_)) ==
    __rest([state EXCEPT !.network[idx] = Append(@, value)])

stream_read(state, self, value, __rest(_)) ==
    LET state2 == [state EXCEPT !.stream = (@ + 1) % BUFFER_SIZE]
    IN  /\ value = state2.stream
        /\ __rest(state2)

====