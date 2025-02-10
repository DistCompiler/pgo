---- MODULE raftkvsValidateDefns ----
EXTENDS Sequences, Integers, FiniteSetsExt

CONSTANTS LogConcat, LogPop

client_reqCh_read(state, self, value, __next(_)) ==
    \* value \in AllReqs is a condition for the spec?
    __next(state)

client_respCh_write(state, self, value, __next(_)) ==
    __next([state EXCEPT !.respCh = value])

network_read(state, self, idx, value, __next(_)) ==
    /\ state.network[idx].enabled = TRUE
    /\ state.network[idx].queue # <<>>
    /\ Head(state.network[idx].queue) = value
    /\ __next([state EXCEPT !.network[idx].queue = Tail(@)])

networkLen_read(state, self, idx, value, __next(_)) ==
    /\ Len(state.network[idx].queue) = value
    /\ __next(state)

network_write(state, self, idx, value, __next(_)) ==
    /\ state.network[idx].enabled = TRUE
    /\ __next([state EXCEPT !.network[idx].queue = Append(@, value)])

fd_read(state, self, idx, value, __next(_)) ==
    /\ state.network[idx].enabled = value
    /\ __next(state)

persistentLog_write(state, self, idx, value, __next(_)) ==
    CASE value.cmd = LogConcat ->
        __next([state EXCEPT !.plog[idx] = @ \o value.entries])
      [] value.cmd = LogPop -> 
        __next([state EXCEPT !.plog[idx] = SubSeq(@, 1, Len(@) - value.cnt)])

becomeLeaderCh_read(state, self, idx, value, __next(_)) ==
    /\ state.becomeLeaderCh[idx] # <<>>
    /\ LET res == Head(state.becomeLeaderCh[idx])
       IN  __next([state EXCEPT !.becomeLeaderCh[idx] = Tail(@)])

becomeLeaderCh_write(state, self, idx, value, __next(_)) ==
    __next([state EXCEPT !.becomeLeaderCh[idx] = Append(@, value)])

appendEntriesCh_read(state, self, idx, value, __next(_)) ==
    /\ state.appendEntriesCh[idx] # <<>>
    /\ LET res == Head(state.appendEntriesCh[idx])
       IN  __next([state EXCEPT !.appendEntriesCh[idx] = Tail(@)])

appendEntriesCh_write(state, self, idx, value, __next(_)) ==
    __next([state EXCEPT !.appendEntriesCh[idx] = Append(@, value)])

====