---------------------------- MODULE except ----------------------------
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
\* Label p of procedure Fizz at line 16 col 12 changed to p_
\* Label p of procedure Buzz at line 21 col 12 changed to p_B
CONSTANT defaultInitValue
VARIABLES n, pc, stack, k, by3, by5

vars == << n, pc, stack, k, by3, by5 >>

ProcSet == {0}

Init == (* Global variables *)
        /\ n = 0
        (* Procedure RunFizzBuzz *)
        /\ k = [ self \in ProcSet |-> defaultInitValue]
        /\ by3 = [ self \in ProcSet |-> defaultInitValue]
        /\ by5 = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "l1"]

p_(self) == /\ pc[self] = "p_"
            /\ PrintT("fizz")
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << n, k, by3, by5 >>

Fizz(self) == p_(self)

p_B(self) == /\ pc[self] = "p_B"
             /\ PrintT("buzz")
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << n, k, by3, by5 >>

Buzz(self) == p_B(self)

p(self) == /\ pc[self] = "p"
           /\ PrintT("fizzbuzz")
           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
           /\ UNCHANGED << n, k, by3, by5 >>

FizzBuzz(self) == p(self)

check3(self) == /\ pc[self] = "check3"
                /\ by3' = [by3 EXCEPT ![self] = (k[self] % 3) = 0]
                /\ pc' = [pc EXCEPT ![self] = "check5"]
                /\ UNCHANGED << n, stack, k, by5 >>

check5(self) == /\ pc[self] = "check5"
                /\ by5' = [by5 EXCEPT ![self] = (k[self] % 5) = 0]
                /\ pc' = [pc EXCEPT ![self] = "printRes"]
                /\ UNCHANGED << n, stack, k, by3 >>

printRes(self) == /\ pc[self] = "printRes"
                  /\ IF by3[self] /\ by5[self]
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
                  /\ UNCHANGED << n, k, by3, by5 >>

ret(self) == /\ pc[self] = "ret"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ by3' = [by3 EXCEPT ![self] = Head(stack[self]).by3]
             /\ by5' = [by5 EXCEPT ![self] = Head(stack[self]).by5]
             /\ k' = [k EXCEPT ![self] = Head(stack[self]).k]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ n' = n

RunFizzBuzz(self) == check3(self) \/ check5(self) \/ printRes(self)
                        \/ ret(self)

l1 == /\ pc[0] = "l1"
      /\ IF n < N
            THEN /\ pc' = [pc EXCEPT ![0] = "inc"]
            ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED << n, stack, k, by3, by5 >>

inc == /\ pc[0] = "inc"
       /\ n' = n + 1
       /\ /\ k' = [k EXCEPT ![0] = n']
          /\ stack' = [stack EXCEPT ![0] = << [ procedure |->  "RunFizzBuzz",
                                                pc        |->  "l1",
                                                by3       |->  by3[0],
                                                by5       |->  by5[0],
                                                k         |->  k[0] ] >>
                                            \o stack[0]]
       /\ by3' = [by3 EXCEPT ![0] = defaultInitValue]
       /\ by5' = [by5 EXCEPT ![0] = defaultInitValue]
       /\ pc' = [pc EXCEPT ![0] = "check3"]

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