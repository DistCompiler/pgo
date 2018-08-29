---------------------------- MODULE ProceduresPSyntax ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT N

(***************************************************************************
--algorithm ProcPSyntax
    variable n = 0;

    macro PrintNum(num) begin
        print num;
    end macro;

    procedure Fizz() begin
        p: print "fizz";
        return;
    end procedure;

    procedure Buzz() begin
        p: print "buzz";
        return;
    end procedure;

    procedure FizzBuzz() begin
        p: print "fizzbuzz";
        return;
    end procedure;

    procedure RunFizzBuzz(k) begin
        check: if ((k % 3 = 0) /\ (k % 5 = 0)) then
                   call FizzBuzz();
               elsif (k % 3 = 0) then
                   call Fizz();
               elsif (k % 5 = 0) then
                   call Buzz();
               else
                   PrintNum(k);
               end if;

        ret: return;
    end procedure;

    process Dummy = 0 begin
        l1: while (n < N) do
            inc: n := n + 1;
            call RunFizzBuzz(n);
        end while;
    end process
end algorithm

 ***************************************************************************)
\* BEGIN TRANSLATION
\* Label p of procedure Fizz at line 15 col 12 changed to p_
\* Label p of procedure Buzz at line 20 col 12 changed to p_B
CONSTANT defaultInitValue
VARIABLES n, pc, stack, k

vars == << n, pc, stack, k >>

ProcSet == {0}

Init == (* Global variables *)
        /\ n = 0
        (* Procedure RunFizzBuzz *)
        /\ k = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "l1"]

p_(self) == /\ pc[self] = "p_"
            /\ PrintT("fizz")
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << n, k >>

Fizz(self) == p_(self)

p_B(self) == /\ pc[self] = "p_B"
             /\ PrintT("buzz")
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << n, k >>

Buzz(self) == p_B(self)

p(self) == /\ pc[self] = "p"
           /\ PrintT("fizzbuzz")
           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
           /\ UNCHANGED << n, k >>

FizzBuzz(self) == p(self)

check(self) == /\ pc[self] = "check"
               /\ IF ((k[self] % 3 = 0) /\ (k[self] % 5 = 0))
                     THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FizzBuzz",
                                                                   pc        |->  "ret" ] >>
                                                               \o stack[self]]
                          /\ pc' = [pc EXCEPT ![self] = "p"]
                     ELSE /\ IF (k[self] % 3 = 0)
                                THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Fizz",
                                                                              pc        |->  "ret" ] >>
                                                                          \o stack[self]]
                                     /\ pc' = [pc EXCEPT ![self] = "p_"]
                                ELSE /\ IF (k[self] % 5 = 0)
                                           THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Buzz",
                                                                                         pc        |->  "ret" ] >>
                                                                                     \o stack[self]]
                                                /\ pc' = [pc EXCEPT ![self] = "p_B"]
                                           ELSE /\ PrintT(k[self])
                                                /\ pc' = [pc EXCEPT ![self] = "ret"]
                                                /\ stack' = stack
               /\ UNCHANGED << n, k >>

ret(self) == /\ pc[self] = "ret"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ k' = [k EXCEPT ![self] = Head(stack[self]).k]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ n' = n

RunFizzBuzz(self) == check(self) \/ ret(self)

l1 == /\ pc[0] = "l1"
      /\ IF (n < N)
            THEN /\ pc' = [pc EXCEPT ![0] = "inc"]
            ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED << n, stack, k >>

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
