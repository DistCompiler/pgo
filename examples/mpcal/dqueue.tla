----------------------------- MODULE dqueue_mpcal -----------------------------
(***************************************************************************)
(* Distributed queue using Modular PlusCal.                                *)
(***************************************************************************)

EXTENDS Naturals, Sequences, TLC
CONSTANT BUFFER_SIZE

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
  archetype AConsumer(consumerNetwork, ref consumerProcessor) {
      c: while (TRUE) {
          (* behavior of reading from network is implementation specific *)
          (* behavior of writing to "processor" is implementation specific *)
          c1: consumerProcessor := consumerNetwork
      }
  }
  
  archetype AProducer(ref producerNetwork, producerStream) {
      p: while (TRUE) {
          p1: producerNetwork := producerStream;
      }
  }
  
  variables queueNetwork = <<>>,
            queueProcessor = 0,
            queueStream = 0;
            
  fair process (Consumer \in {0,1}) == instance AConsumer(queueNetwork, ref queueProcessor)
      mapping queueNetwork via LossyNetwork;
  fair process (Producer = 2) == instance AProducer(ref queueNetwork, ref queueStream)
      mapping queueNetwork via LossyNetwork
      mapping queueStream via CyclicReads;
}
***************************************************************************)


(***************************************************************************
--algorithm DistQueue {
    variables queueNetwork = <<>>,
              queueProcessor = 0,
              queueStream = 1;
              
    fair process (Consumer \in {0,1})
    variables tmp0;
    {
        c: while (TRUE) {
            c1: await Len(queueNetwork) > 0;
                with (msg = Head(queueNetwork)) {
                    queueNetwork := Tail(queueNetwork);
                    tmp0 := msg;
                };
                queueProcessor := tmp0;
        }
    }
    
    fair process (Producer = 2)
    variables tmp0, tmp1;
    {
        p: while(TRUE) {
           p1: either {
                   tmp0 := queueNetwork
               } or {
                   queueStream := (queueStream + 1) % BUFFER_SIZE;
                   tmp1 := queueStream;
                   await Len(queueNetwork) < BUFFER_SIZE;
                   tmp0 := Append(queueNetwork, tmp1);
               };
               queueNetwork := tmp0;
        }
    }

}
***************************************************************************)
\* BEGIN TRANSLATION
\* Process variable tmp0 of process Consumer at line 74 col 15 changed to tmp0_
CONSTANT defaultInitValue
VARIABLES queueNetwork, queueProcessor, queueStream, pc, tmp0_, tmp0, tmp1

vars == << queueNetwork, queueProcessor, queueStream, pc, tmp0_, tmp0, tmp1 >>

ProcSet == ({0,1}) \cup {2}

Init == (* Global variables *)
        /\ queueNetwork = <<>>
        /\ queueProcessor = 0
        /\ queueStream = 1
        (* Process Consumer *)
        /\ tmp0_ = [self \in {0,1} |-> defaultInitValue]
        (* Process Producer *)
        /\ tmp0 = defaultInitValue
        /\ tmp1 = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self \in {0,1} -> "c"
                                        [] self = 2 -> "p"]

c(self) == /\ pc[self] = "c"
           /\ pc' = [pc EXCEPT ![self] = "c1"]
           /\ UNCHANGED << queueNetwork, queueProcessor, queueStream, tmp0_, tmp0, tmp1 >>

c1(self) == /\ pc[self] = "c1"
            /\ Len(queueNetwork) > 0
            /\ LET msg == Head(queueNetwork) IN
                 /\ queueNetwork' = Tail(queueNetwork)
                 /\ tmp0_' = [tmp0_ EXCEPT ![self] = msg]
            /\ queueProcessor' = tmp0_'[self]
            /\ pc' = [pc EXCEPT ![self] = "c"]
            /\ UNCHANGED << queueStream, tmp0, tmp1 >>

Consumer(self) == c(self) \/ c1(self)

p == /\ pc[2] = "p"
     /\ pc' = [pc EXCEPT ![2] = "p1"]
     /\ UNCHANGED << queueNetwork, queueProcessor, queueStream, tmp0_, tmp0, tmp1 >>

p1 == /\ pc[2] = "p1"
      /\ \/ /\ tmp0' = queueNetwork
            /\ UNCHANGED <<queueStream, tmp1>>
         \/ /\ queueStream' = (queueStream + 1) % BUFFER_SIZE
            /\ tmp1' = queueStream'
            /\ Len(queueNetwork) < BUFFER_SIZE
            /\ tmp0' = Append(queueNetwork, tmp1')
      /\ queueNetwork' = tmp0'
      /\ pc' = [pc EXCEPT ![2] = "p"]
      /\ UNCHANGED << queueProcessor, tmp0_ >>

Producer == p \/ p1

Next == Producer
           \/ (\E self \in {0,1}: Consumer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {0,1} : WF_vars(Consumer(self))
        /\ WF_vars(Producer)

\* END TRANSLATION

\* Basic invariant
ProducerConsumer == queueStream - queueProcessor <= BUFFER_SIZE+1

\* Messages produced are eventually consumed
\* Not satisfied because message loss is not accounted for
EventuallyConsumed == \A n \in 0..BUFFER_SIZE : (queueStream = n) => <>(queueProcessor = n)

=============================================================================
\* Modification History
\* Last modified Fri Sep 28 16:49:58 PDT 2018 by rmc
\* Last modified Wed Oct 12 02:41:48 PDT 2011 by lamport
\* Created Mon Oct 10 06:26:47 PDT 2011 by lamport
