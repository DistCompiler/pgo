----------------------------- MODULE test -----------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

(***************************************************************************
--mpcal test {

(* *)
procedure inc(self_, ref counter) {
    inc1: counter := counter + 1;
    inc2: return;
}

(* *)
archetype Counter(ref out)
variables value;
{
    c0: value := 0;
    c1: call inc(self, ref value);
    c2: out := value;
}

  variables out;

  process (Server = "1") == instance Counter(ref out);
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm test {
    variables n = 0, counterRead;
    procedure inc0 (self_)
    variables returnValueRead, returnValueWrite;
    {
        inc1:
            returnValueRead := n;
            returnValueWrite := (returnValueRead) + (1);
            n := returnValueWrite;
        inc2:
            return;

    }
    process (Server = "1")
    variables value;
    {
        c1:
            call inc0(self);
        c2:
            counterRead := n;
            print counterRead;

    }
}
\* END PLUSCAL TRANSLATION




***************************************************************************)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES n, rpcQueue, counterRead, pc, stack, self_, returnValueWrite, value

vars == << n, rpcQueue, counterRead, pc, stack, self_, returnValueWrite,
           value >>

ProcSet == ({"Server"})

Init == (* Global variables *)
        /\ n = 0
        /\ rpcQueue = [r \in {"Server", "Runner"} |-> <<>>]
        /\ counterRead = defaultInitValue
        (* Procedure inc0 *)
        /\ self_ = [ self \in ProcSet |-> defaultInitValue]
        /\ returnValueWrite = [ self \in ProcSet |-> defaultInitValue]
        (* Process Server *)
        /\ value = [self \in {"Server"} |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "c1"]

inc1(self) == /\ pc[self] = "inc1"
              /\ returnValueWrite' = [returnValueWrite EXCEPT ![self] = 1]
              /\ n' = returnValueWrite'[self]
              /\ pc' = [pc EXCEPT ![self] = "inc2"]
              /\ UNCHANGED << rpcQueue, counterRead, stack, self_, value >>

inc2(self) == /\ pc[self] = "inc2"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ returnValueWrite' = [returnValueWrite EXCEPT ![self] = Head(stack[self]).returnValueWrite]
              /\ self_' = [self_ EXCEPT ![self] = Head(stack[self]).self_]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << n, rpcQueue, counterRead, value >>

inc0(self) == inc1(self) \/ inc2(self)

c1(self) == /\ pc[self] = "c1"
            /\ /\ self_' = [self_ EXCEPT ![self] = self]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "inc0",
                                                        pc        |->  "c3",
                                                        returnValueWrite |->  returnValueWrite[self],
                                                        self_     |->  self_[self] ] >>
                                                    \o stack[self]]
            /\ returnValueWrite' = [returnValueWrite EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "inc1"]
            /\ UNCHANGED << n, rpcQueue, counterRead, value >>

c3(self) == /\ pc[self] = "c3"
            /\ counterRead' = n
            /\ PrintT(counterRead')
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << n, rpcQueue, stack, self_, returnValueWrite, value >>

Server(self) == c1(self) \/ c3(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: inc0(self))
           \/ (\E self \in {"Server"}: Server(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================