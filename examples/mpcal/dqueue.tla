----------------------------- MODULE dqueue_mpcal -----------------------------
(***************************************************************************)
(* Distributed queue using Modular PlusCal.                                *)
(***************************************************************************)

EXTENDS Naturals, Sequences, TLC
CONSTANT BUFFER_SIZE

ProducerId == 0
CONSTANT NUM_CONSUMERS

(* total nodes in the system: number of consumers + the producer *)
NUM_NODES == NUM_CONSUMERS + 1

(***************************************************************************
--mpcal DistQueue {
  mapping macro TCPChannel {
      read {
          await Len($variable[self]) > 0;
          with (msg = Head($variable[self])) {
              $variable := Tail($variable[self]);
              yield msg;
          };
      }

      write {
          await Len($variable[self]) < BUFFER_SIZE;
          yield Append($variable[self], $value);
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
  archetype AConsumer(ref network, ref processor) {
      c: while (TRUE) {
          (* request more data to the producer by sending your own identifier
             over the network *)
          c1: network[ProducerId] := self;

          (* processes the piece of data the producer sends back over the network
             by writing to a "processor" abstract interface *)
          c2: processor := network[ProducerId];
      }
  }

  archetype AProducer(ref network, stream)
  variable requester; {
      p: while (TRUE) {
          (* wait for a consumer to request data *)
          p1: requester := network[self];

          (* send some data to the requester coming from a "stream" abstract interface *)
          p2: network[requester] := stream;
      }
  }

  variables network = [id in 0..NUM_NODES |-> <<>>]],
            processor = 0,
            stream = 0;

  fair process (Consumer \in 1..NUM_CONSUMERS) == instance AConsumer(ref network, ref processor)
      mapping network[_] via TCPChannel;
  fair process (Producer = ProducerId) == instance AProducer(ref network, ref stream)
      mapping network[_] via TCPChannel
      mapping stream via CyclicReads;
}
***************************************************************************)
=============================================================================
\* Modification History
\* Last modified Sun Dec 02 13:59:03 PST 2018 by rmc
\* Last modified Wed Oct 12 02:41:48 PDT 2011 by lamport
\* Created Mon Oct 10 06:26:47 PDT 2011 by lamport