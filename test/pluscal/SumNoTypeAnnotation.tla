----------------------------- MODULE Sum ----------------------------
EXTENDS Naturals, Sequences, TLC
CONSTANT MAXINT, RUNS, N

(* PlusCal options (-termination) *)

(*

--algorithm Sum  {
variables network = [i \in 1 .. N+1 |-> <<>>];

macro SendTo(from, to, msg) {
    network[to] := Append(network[to], <<from, msg>>);
}

macro Recv(to, id, msg) {
    await network[to] # <<>>;
    id := Head(network[to])[1];
    msg := Head(network[to])[2];
    network[to] := Tail(network[to]);
}

process (Client \in 1..N)
  variable a_init, b_init, runs=0, id, msg, sum;
  {
    cl: while (runs < RUNS) {
      with (vala \in 1..MAXINT,
           valb \in 1..MAXINT) {

        a_init := vala;
        b_init := valb;
      };
      runs := runs + 1;
      cs:
        SendTo(self, N+1, <<a_init,b_init>>);
      cr:
        Recv(self, id, msg);
        sum := msg;
      chk: skip;
        \* assert(sum = a_init - b_init);
    }
}

process (Server = N+1)
  variable a, b, id, msg;
  {
  sr:
    Recv(N+1, id, msg);
    a := msg[1];
    b := msg[2];
  ss:
    SendTo(N+1, id, a+b);
    goto sr;
}

}
*)

\* BEGIN TRANSLATION
\* Process variable id of process Client at line 23 col 36 changed to id_
\* Process variable msg of process Client at line 23 col 40 changed to msg_
CONSTANT defaultInitValue
VARIABLES network, pc, a_init, b_init, runs, id_, msg_, sum, a, b, id, msg

vars == << network, pc, a_init, b_init, runs, id_, msg_, sum, a, b, id, msg
        >>

ProcSet == (1..N) \cup {N+1}

Init == (* Global variables *)
        /\ network = [i \in 1 .. N+1 |-> <<>>]
        (* Process Client *)
        /\ a_init = [self \in 1..N |-> defaultInitValue]
        /\ b_init = [self \in 1..N |-> defaultInitValue]
        /\ runs = [self \in 1..N |-> 0]
        /\ id_ = [self \in 1..N |-> defaultInitValue]
        /\ msg_ = [self \in 1..N |-> defaultInitValue]
        /\ sum = [self \in 1..N |-> defaultInitValue]
        (* Process Server *)
        /\ a = defaultInitValue
        /\ b = defaultInitValue
        /\ id = defaultInitValue
        /\ msg = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self \in 1..N -> "cl"
                                        [] self = N+1 -> "sr"]

cl(self) == /\ pc[self] = "cl"
            /\ IF runs[self] < RUNS
                  THEN /\ \E vala \in 1..MAXINT:
                            \E valb \in 1..MAXINT:
                              /\ a_init' = [a_init EXCEPT ![self] = vala]
                              /\ b_init' = [b_init EXCEPT ![self] = valb]
                       /\ runs' = [runs EXCEPT ![self] = runs[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "cs"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << a_init, b_init, runs >>
            /\ UNCHANGED << network, id_, msg_, sum, a, b, id, msg >>

cs(self) == /\ pc[self] = "cs"
            /\ network' = [network EXCEPT ![(N+1)] = Append(network[(N+1)], <<self, (<<a_init[self],b_init[self]>>)>>)]
            /\ pc' = [pc EXCEPT ![self] = "cr"]
            /\ UNCHANGED << a_init, b_init, runs, id_, msg_, sum, a, b, id,
                            msg >>

cr(self) == /\ pc[self] = "cr"
            /\ network[self] # <<>>
            /\ id_' = [id_ EXCEPT ![self] = Head(network[self])[1]]
            /\ msg_' = [msg_ EXCEPT ![self] = Head(network[self])[2]]
            /\ network' = [network EXCEPT ![self] = Tail(network[self])]
            /\ sum' = [sum EXCEPT ![self] = msg_'[self]]
            /\ pc' = [pc EXCEPT ![self] = "chk"]
            /\ UNCHANGED << a_init, b_init, runs, a, b, id, msg >>

chk(self) == /\ pc[self] = "chk"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "cl"]
             /\ UNCHANGED << network, a_init, b_init, runs, id_, msg_, sum, a,
                             b, id, msg >>

Client(self) == cl(self) \/ cs(self) \/ cr(self) \/ chk(self)

sr == /\ pc[N+1] = "sr"
      /\ network[(N+1)] # <<>>
      /\ id' = Head(network[(N+1)])[1]
      /\ msg' = Head(network[(N+1)])[2]
      /\ network' = [network EXCEPT ![(N+1)] = Tail(network[(N+1)])]
      /\ a' = msg'[1]
      /\ b' = msg'[2]
      /\ pc' = [pc EXCEPT ![N+1] = "ss"]
      /\ UNCHANGED << a_init, b_init, runs, id_, msg_, sum >>

ss == /\ pc[N+1] = "ss"
      /\ network' = [network EXCEPT ![id] = Append(network[id], <<(N+1), (a+b)>>)]
      /\ pc' = [pc EXCEPT ![N+1] = "sr"]
      /\ UNCHANGED << a_init, b_init, runs, id_, msg_, sum, a, b, id, msg >>

Server == sr \/ ss

Next == Server
           \/ (\E self \in 1..N: Client(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(Client(self))
        /\ WF_vars(Server)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

SendRecv == pc[N+1] = "ss" => a = a_init[id] /\ b = b_init[id]
Sum == \A i \in 1..N : pc[i] = "chk" => sum[i] = a_init[i] + b_init[i]

THEOREM Spec => []SendRecv
THEOREM Spec => []Sum

=============
