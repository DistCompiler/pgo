---------------------------- MODULE Procedures ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT N

(***************************************************************************
--algorithm Procedures
{
    macro PrintNum(num) {
        print num;
    }

    procedure Fizz() {
        p: print "fizz";
        return;
    }

    procedure Buzz() {
        p: print "buzz";
        return;
    }

    procedure FizzBuzz() {
        p: print "fizzbuzz";
        return;
    }

    procedure RunFizzBuzz(k) {
        check: if ((k % 3 = 0) /\ (k % 5 = 0)) {
                   call FizzBuzz();
               } else if (k % 3 = 0) {
                   call Fizz();
               } else if (k % 5 = 0) {
                   call Buzz();
               } else {
                   PrintNum(k);
               };

        ret: return;
    }

    process (Dummy = 0)
    variable n = 0; {
        l1: while (n < N) {
            inc: n := n + 1;
            call RunFizzBuzz(n);
        }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
\* Label p of procedure Fizz at line 14 col 12 changed to p_
\* Label p of procedure Buzz at line 19 col 12 changed to p_B
CONSTANT defaultInitValue
VARIABLES pc, stack, k, n

vars == << pc, stack, k, n >>

ProcSet == {0}

Init == (* Procedure RunFizzBuzz *)
        /\ k = [ self \in ProcSet |-> defaultInitValue]
        (* Process Dummy *)
        /\ n = 0
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "l1"]

p_(self) == /\ pc[self] = "p_"
            /\ PrintT("fizz")
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << k, n >>

Fizz(self) == p_(self)

p_B(self) == /\ pc[self] = "p_B"
             /\ PrintT("buzz")
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << k, n >>

Buzz(self) == p_B(self)

p(self) == /\ pc[self] = "p"
           /\ PrintT("fizzbuzz")
           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
           /\ UNCHANGED << k, n >>

FizzBuzz(self) == p(self)

check(self) == /\ pc[self] = "check"
               /\ IF (k[self] % 3 = 0) /\ (k[self] % 5 = 0)
                     THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FizzBuzz",
                                                                   pc        |->  "ret" ] >>
                                                               \o stack[self]]
                          /\ pc' = [pc EXCEPT ![self] = "p"]
                     ELSE /\ IF k[self] % 3 = 0
                                THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Fizz",
                                                                              pc        |->  "ret" ] >>
                                                                          \o stack[self]]
                                     /\ pc' = [pc EXCEPT ![self] = "p_"]
                                ELSE /\ IF k[self] % 5 = 0
                                           THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Buzz",
                                                                                         pc        |->  "ret" ] >>
                                                                                     \o stack[self]]
                                                /\ pc' = [pc EXCEPT ![self] = "p_B"]
                                           ELSE /\ PrintT(k[self])
                                                /\ pc' = [pc EXCEPT ![self] = "ret"]
                                                /\ stack' = stack
               /\ UNCHANGED << k, n >>

ret(self) == /\ pc[self] = "ret"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ k' = [k EXCEPT ![self] = Head(stack[self]).k]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ n' = n

RunFizzBuzz(self) == check(self) \/ ret(self)

l1 == /\ pc[0] = "l1"
      /\ IF n < N
            THEN /\ pc' = [pc EXCEPT ![0] = "inc"]
            ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED << stack, k, n >>

inc == /\ pc[0] = "inc"
       /\ n' = n + 1
       /\ /\ k' = [k EXCEPT ![0] = n']
          /\ stack' = [stack EXCEPT ![0] = << [ procedure |->  "RunFizzBuzz",
                                                pc        |->  "l1",
                                                k         |->  k[0] ] >>
                                            \o stack[0]]
       /\ pc' = [pc EXCEPT ![0] = "check"]

Dummy == l1 \/ inc

Next == Dummy
           \/ (\E self \in ProcSet:  \/ Fizz(self) \/ Buzz(self) \/ FizzBuzz(self)
                                     \/ RunFizzBuzz(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================