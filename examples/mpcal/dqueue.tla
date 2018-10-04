----------------------------- MODULE dqueue_mpcal -----------------------------
(***************************************************************************)
(* Distributed queue using Modular PlusCal.                                *)
(***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT BUFFER_SIZE
CONSTANT NUM_CONSUMERS


(***************************************************************************
--mpcal DistQueue {
  mapping macro LossyNetwork {
      read {
          await Len($variable) > 0;
          with (msg = Head($variable)) {
              $variable := Tail($variable);
              yield msg;
          };
      }

      write {
          either {
              yield $variable
          } or {
              await Len($variable) < BUFFER_SIZE;
              yield Append($variable, $value);
          }
      }
  }

  mapping macro CyclicReads {
      read  {
          $variable := ($variable + 1) % BUFFER_SIZE;
          yield $variable;

      }

      write { yield $variable }
  }

  (* consumer: Processes one element read from the network at a time, infinitely *)
  archetype AConsumer(network, ref processor) {
      c: while (TRUE) {
          network := self;
          processor := network;

      }
  }

  archetype AProducer(ref network, stream)
  variables requester; {
      p: while (TRUE) {
          requester := network;
          network[requester] := stream;
      }
  }

    variables network = [c \in 1..NUM_CONSUMERS |-> <<>>],
            processor = 0,
            stream = 0;

  fair process (Consumer \in 1..NUM_CONSUMERS) == instance AConsumer(network[self], ref processor)
      mapping network via LossyNetwork;
  fair process (Producer = NUM_CONSUMERS+1) == instance AProducer(ref network, ref stream)
      mapping network via LossyNetwork
      mapping stream via CyclicReads;
}
***************************************************************************)


(***************************************************************************
--algorithm DistQueue {
    variables network = <<>>,
              processor = 0,
              stream = 1;

    fair process (Consumer \in {0,1})
    variables tmp0;
    {
        c: while (TRUE) {
            c1: await Len(network) > 0;
                with (msg = Head(network)) {
                    network := Tail(network);
                    tmp0 := msg;
                };
                processor := tmp0;
        }
    }

    fair process (Producer = 2)
    variables tmp0, tmp1;
    {
        p: while(TRUE) {
           p1: either {
                   tmp0 := network
               } or {
                   stream := (stream + 1) % BUFFER_SIZE;
                   tmp1 := stream;
                   await Len(network) < BUFFER_SIZE;
                   tmp0 := Append(network, tmp1);
               };
               network := tmp0;
        }
    }

}
***************************************************************************)
\* BEGIN TRANSLATION
\* Process variable tmp0 of process Consumer at line 75 col 15 changed to tmp0_
CONSTANT defaultInitValue
VARIABLES network, processor, stream, pc, tmp0_, tmp0, tmp1

vars == << network, processor, stream, pc, tmp0_, tmp0, tmp1 >>

ProcSet == ({0,1}) \cup {2}

Init == (* Global variables *)
        /\ network = <<>>
        /\ processor = 0
        /\ stream = 1
        (* Process Consumer *)
        /\ tmp0_ = [self \in {0,1} |-> defaultInitValue]
        (* Process Producer *)
        /\ tmp0 = defaultInitValue
        /\ tmp1 = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self \in {0,1} -> "c"
                                        [] self = 2 -> "p"]

c(self) == /\ pc[self] = "c"
           /\ pc' = [pc EXCEPT ![self] = "c1"]
           /\ UNCHANGED << network, processor, stream, tmp0_, tmp0, tmp1 >>

c1(self) == /\ pc[self] = "c1"
            /\ Len(network) > 0
            /\ LET msg == Head(network) IN
                 /\ network' = Tail(network)
                 /\ tmp0_' = [tmp0_ EXCEPT ![self] = msg]
            /\ processor' = tmp0_'[self]
            /\ pc' = [pc EXCEPT ![self] = "c"]
            /\ UNCHANGED << stream, tmp0, tmp1 >>

Consumer(self) == c(self) \/ c1(self)

p == /\ pc[2] = "p"
     /\ pc' = [pc EXCEPT ![2] = "p1"]
     /\ UNCHANGED << network, processor, stream, tmp0_, tmp0, tmp1 >>

p1 == /\ pc[2] = "p1"
      /\ \/ /\ tmp0' = network
            /\ UNCHANGED <<stream, tmp1>>
         \/ /\ stream' = (stream + 1) % BUFFER_SIZE
            /\ tmp1' = stream'
            /\ Len(network) < BUFFER_SIZE
            /\ tmp0' = Append(network, tmp1')
      /\ network' = tmp0'
      /\ pc' = [pc EXCEPT ![2] = "p"]
      /\ UNCHANGED << processor, tmp0_ >>

Producer == p \/ p1

Next == Producer
           \/ (\E self \in {0,1}: Consumer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {0,1} : WF_vars(Consumer(self))
        /\ WF_vars(Producer)

\* END TRANSLATION

\* Basic invariant
ProducerConsumer == stream - processor <= BUFFER_SIZE+1

\* Messages produced are eventually consumed
\* Not satisfied because message loss is not accounted for
EventuallyConsumed == \A n \in 0..BUFFER_SIZE : (stream = n) => <>(processor = n)

=============================================================================
\* Modification History
\* Last modified Thu Oct 04 11:38:51 PDT 2018 by rmc
\* Last modified Wed Oct 12 02:41:48 PDT 2011 by lamport
\* Created Mon Oct 10 06:26:47 PDT 2011 by lamport
