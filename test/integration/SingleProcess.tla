---------------------------- MODULE SingleProcess ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT N

(***************************************************************************
--algorithm SingleProcess
{
    variable n = 0;

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

    {
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
VARIABLES n, pc, stack, k

vars == << n, pc, stack, k >>

Init == (* Global variables *)
        /\ n = 0
        (* Procedure RunFizzBuzz *)
        /\ k = defaultInitValue
        /\ stack = << >>
        /\ pc = "l1"

p_ == /\ pc = "p_"
      /\ PrintT("fizz")
      /\ pc' = Head(stack).pc
      /\ stack' = Tail(stack)
      /\ UNCHANGED << n, k >>

Fizz == p_

p_B == /\ pc = "p_B"
       /\ PrintT("buzz")
       /\ pc' = Head(stack).pc
       /\ stack' = Tail(stack)
       /\ UNCHANGED << n, k >>

Buzz == p_B

p == /\ pc = "p"
     /\ PrintT("fizzbuzz")
     /\ pc' = Head(stack).pc
     /\ stack' = Tail(stack)
     /\ UNCHANGED << n, k >>

FizzBuzz == p

check == /\ pc = "check"
         /\ IF (k % 3 = 0) /\ (k % 5 = 0)
               THEN /\ stack' = << [ procedure |->  "FizzBuzz",
                                     pc        |->  "ret" ] >>
                                 \o stack
                    /\ pc' = "p"
               ELSE /\ IF k % 3 = 0
                          THEN /\ stack' = << [ procedure |->  "Fizz",
                                                pc        |->  "ret" ] >>
                                            \o stack
                               /\ pc' = "p_"
                          ELSE /\ IF k % 5 = 0
                                     THEN /\ stack' = << [ procedure |->  "Buzz",
                                                           pc        |->  "ret" ] >>
                                                       \o stack
                                          /\ pc' = "p_B"
                                     ELSE /\ PrintT(k)
                                          /\ pc' = "ret"
                                          /\ stack' = stack
         /\ UNCHANGED << n, k >>

ret == /\ pc = "ret"
       /\ pc' = Head(stack).pc
       /\ k' = Head(stack).k
       /\ stack' = Tail(stack)
       /\ n' = n

RunFizzBuzz == check \/ ret

l1 == /\ pc = "l1"
      /\ IF n < N
            THEN /\ pc' = "inc"
            ELSE /\ pc' = "Done"
      /\ UNCHANGED << n, stack, k >>

inc == /\ pc = "inc"
       /\ n' = n + 1
       /\ /\ k' = n'
          /\ stack' = << [ procedure |->  "RunFizzBuzz",
                           pc        |->  "l1",
                           k         |->  k ] >>
                       \o stack
       /\ pc' = "check"

Next == Fizz \/ Buzz \/ FizzBuzz \/ RunFizzBuzz \/ l1 \/ inc
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================