----------------------------- MODULE dqueue_mpcal -----------------------------
(***************************************************************************)
(* Distributed queue using Modular PlusCal.                                *)
(***************************************************************************)

EXTENDS Naturals, Sequences, TLC

CONSTANTS BUFFER_SIZE, NUM_CONSUMERS, PRODUCER

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
  archetype AConsumer(ref net, ref proc) {
      c: while (TRUE) {
          (* request more data to the producer by sending your own identifier
             over the network *)
          c1: net[PRODUCER] := self;

          (* processes the piece of data the producer sends back over the network
             by writing to a "processor" abstract interface *)
          c2: proc := net[PRODUCER];
      }
  }

  archetype AProducer(ref net, s)
  variable requester; {
      p: while (TRUE) {
          (* wait for a consumer to request data *)
          p1: requester := net[self];

          (* send some data to the requester coming from a "stream" abstract interface *)
          p2: net[requester] := s;
      }
  }

  variables network = [id \in 0..NUM_NODES |-> <<>>],
            processor = 0,
            stream = 0;

  fair process (Consumer \in 1..NUM_CONSUMERS) == instance AConsumer(ref network, ref processor)
      mapping network[_] via TCPChannel;
  fair process (Producer = PRODUCER) == instance AProducer(ref network, ref stream)
      mapping network[_] via TCPChannel
      mapping stream via CyclicReads;
}
***************************************************************************)
=============================================================================
\* Modification History
\* Last modified Tue Jan 15 13:07:55 PST 2019 by rmc
\* Last modified Wed Oct 12 02:41:48 PDT 2011 by lamport
\* Created Mon Oct 10 06:26:47 PDT 2011 by lamport