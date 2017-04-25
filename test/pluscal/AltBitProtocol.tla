--------------------- MODULE AltBitProtocol  ----------------------
EXTENDS Naturals, Sequences, TLC
CONSTANT Msg

(******************************************************)
(* AltBitProtocol from The PlusCal Algorithm Language *)
(* paper by Lamport                                   *)
(******************************************************)

Remove(i, seq) == [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]

(*
--algorithm AltBitProtocol {
  variables 
    input = <<>>, output = <<>>,
    msgChan = <<>>, ackChan = <<>>,
    newChan = <<>>;

  macro Send(m, chan) {
    chan := Append(chan, m);
  }

  macro Recv(v, chan) {
    await chan # <<>>;  \* could also do Len(chan) > 0 ??
    v := Head(chan);
    chan := Tail(chan);
  }
   
  process (Sender = "S")
    variables next = 1, sbit = 0, ack;
  {
  s:  while (TRUE) {
        either with (m \in Msg) {
          input := Append(input, m);

        } or {
          await next <= Len(input);
          Send(<<input[next], sbit>>, msgChan);

        } or {
          Recv(ack, ackChan);
          if (ack = sbit) {
            next := next + 1;
            sbit := (sbit + 1) % 2;
          };
        };
        print <<"Sender", input>>;
      }
  }; \* end Sender process block

  process (Receiver = "R") 
    variables rbit = 1, msg;
  {
  r:  while (TRUE) {
        either {
          Send(rbit, ackChan);
        } or {
          Recv(msg, msgChan);
          if (msg[2] # rbit) {
            rbit := (rbit + 1) % 2;
            output := Append(output, msg[1]);
          };
        };
      }
  }; \* end Receiver process block

  process (LoseMsg = "L") {
  l:  while (TRUE) {
        either with (i \in 1..Len(msgChan)) {
          msgChan := Remove(i, msgChan);
        } or with (i \in 1..Len(ackChan)) {
          ackChan := Remove(i, ackChan);
        };
      }  
  }; \* end LoseMsg process block

} \* end algorithm
*)    
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES input, output, msgChan, ackChan, newChan, next, sbit, ack, rbit, 
          msg

vars == << input, output, msgChan, ackChan, newChan, next, sbit, ack, rbit, 
           msg >>

ProcSet == {"S"} \cup {"R"} \cup {"L"}

Init == (* Global variables *)
        /\ input = <<>>
        /\ output = <<>>
        /\ msgChan = <<>>
        /\ ackChan = <<>>
        /\ newChan = <<>>
        (* Process Sender *)
        /\ next = 1
        /\ sbit = 0
        /\ ack = defaultInitValue
        (* Process Receiver *)
        /\ rbit = 1
        /\ msg = defaultInitValue

Sender == /\ \/ /\ \E m \in Msg:
                     input' = Append(input, m)
                /\ UNCHANGED <<msgChan, ackChan, next, sbit, ack>>
             \/ /\ next <= Len(input)
                /\ msgChan' = Append(msgChan, (<<input[next], sbit>>))
                /\ UNCHANGED <<input, ackChan, next, sbit, ack>>
             \/ /\ ackChan # <<>>
                /\ ack' = Head(ackChan)
                /\ ackChan' = Tail(ackChan)
                /\ IF ack' = sbit
                      THEN /\ next' = next + 1
                           /\ sbit' = (sbit + 1) % 2
                      ELSE /\ TRUE
                           /\ UNCHANGED << next, sbit >>
                /\ UNCHANGED <<input, msgChan>>
          /\ PrintT(<<"Sender", input'>>)
          /\ UNCHANGED << output, newChan, rbit, msg >>

Receiver == /\ \/ /\ ackChan' = Append(ackChan, rbit)
                  /\ UNCHANGED <<output, msgChan, rbit, msg>>
               \/ /\ msgChan # <<>>
                  /\ msg' = Head(msgChan)
                  /\ msgChan' = Tail(msgChan)
                  /\ IF msg'[2] # rbit
                        THEN /\ rbit' = (rbit + 1) % 2
                             /\ output' = Append(output, msg'[1])
                        ELSE /\ TRUE
                             /\ UNCHANGED << output, rbit >>
                  /\ UNCHANGED ackChan
            /\ UNCHANGED << input, newChan, next, sbit, ack >>

LoseMsg == /\ \/ /\ \E i \in 1..Len(msgChan):
                      msgChan' = Remove(i, msgChan)
                 /\ UNCHANGED ackChan
              \/ /\ \E i \in 1..Len(ackChan):
                      ackChan' = Remove(i, ackChan)
                 /\ UNCHANGED msgChan
           /\ UNCHANGED << input, output, newChan, next, sbit, ack, rbit, msg >>

Next == Sender \/ Receiver \/ LoseMsg

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

==================================================================
