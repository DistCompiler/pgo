----------------------------- MODULE dqueue -----------------------------
(***************************************************************************)
(* Distributed queue using Modular PlusCal.                                *)
(***************************************************************************)

EXTENDS Naturals, Sequences, TLC

CONSTANTS BUFFER_SIZE, NUM_CONSUMERS, PRODUCER


(***************************************************************************
--mpcal dqueue {
  define {
    (* total nodes in the system: number of consumers + the producer *)
    NUM_NODES == NUM_CONSUMERS + 1
  }

  mapping macro TCPChannel {
      read {
          await Len($variable) > 0;
          with (msg = Head($variable)) {
              $variable := Tail($variable);
              yield msg;
          };
      }

      write {
          await Len($variable) < BUFFER_SIZE;
          yield Append($variable, $value);
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
  archetype AConsumer(ref net[_], ref proc) {
      c: while (TRUE) {
          (* request more data to the producer by sending your own identifier
             over the network *)
          c1: net[PRODUCER] := self;

          (* processes the piece of data the producer sends back over the network
             by writing to a "processor" abstract interface *)
          c2: proc := net[self];
      }
  }

  archetype AProducer(ref net[_], ref s)
  variable requester; {
      p: while (TRUE) {
          (* wait for a consumer to request data *)
          p1: requester := net[self];

          (* send some data to the requester coming from a "stream" abstract interface *)
          p2: net[requester] := s;
      }
  }

  variables network = [id \in 0..NUM_NODES-1 |-> <<>>],
            processor = 0,
            stream = 0;

  fair process (Consumer \in 1..NUM_CONSUMERS) == instance AConsumer(ref network[_], ref processor)
      mapping network[_] via TCPChannel;
  fair process (Producer \in {PRODUCER}) == instance AProducer(ref network[_], ref stream)
      mapping network[_] via TCPChannel
      mapping stream via CyclicReads;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm dqueue {
  variables network = [id \in (0) .. ((NUM_NODES) - (1)) |-> <<>>]; processor = 0; stream = 0;
  define{
    NUM_NODES == (NUM_CONSUMERS) + (1)
  }
  
  fair process (Consumer \in (1) .. (NUM_CONSUMERS))
  {
    c:
      if (TRUE) {
        goto c1;
      } else {
        goto Done;
      };
    c1:
      with (value1 = self) {
        await (Len((network)[PRODUCER])) < (BUFFER_SIZE);
        network := [network EXCEPT ![PRODUCER] = Append((network)[PRODUCER], value1)];
        goto c2;
      };
    c2:
      await (Len((network)[self])) > (0);
      with (msg00 = Head((network)[self])) {
        network := [network EXCEPT ![self] = Tail((network)[self])];
        with (yielded_network1 = msg00) {
          processor := yielded_network1;
          goto c;
        };
      };
  }
  
  fair process (Producer \in {PRODUCER})
    variables requester;
  {
    p:
      if (TRUE) {
        goto p1;
      } else {
        goto Done;
      };
    p1:
      await (Len((network)[self])) > (0);
      with (msg10 = Head((network)[self])) {
        network := [network EXCEPT ![self] = Tail((network)[self])];
        with (yielded_network00 = msg10) {
          requester := yielded_network00;
          goto p2;
        };
      };
    p2:
      stream := ((stream) + (1)) % (BUFFER_SIZE);
      with (
        yielded_stream0 = stream, 
        value00 = yielded_stream0
      ) {
        await (Len((network)[requester])) < (BUFFER_SIZE);
        network := [network EXCEPT ![requester] = Append((network)[requester], value00)];
        goto p;
      };
  }
}

\* END PLUSCAL TRANSLATION
*)

\* BEGIN TRANSLATION PCal-e64ab9284c1a4c5172f564abb6f099c4
CONSTANT defaultInitValue
VARIABLES pc, network, processor, stream

(* define statement *)
NUM_NODES == (NUM_CONSUMERS) + (1)

VARIABLE requester

vars == << pc, network, processor, stream, requester >>

ProcSet == ((1) .. (NUM_CONSUMERS)) \cup ({PRODUCER})

Init == (* Global variables *)
        /\ network = [id \in (0) .. ((NUM_NODES) - (1)) |-> <<>>]
        /\ processor = 0
        /\ stream = 0
        (* Process Producer *)
        /\ requester = [self \in {PRODUCER} |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in (1) .. (NUM_CONSUMERS) -> "c"
                                        [] self \in {PRODUCER} -> "p"]

c(self) == /\ pc[self] = "c"
           /\ IF TRUE
                 THEN /\ pc' = [pc EXCEPT ![self] = "c1"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << network, processor, stream, requester >>

c1(self) == /\ pc[self] = "c1"
            /\ LET value1 == self IN
                 /\ (Len((network)[PRODUCER])) < (BUFFER_SIZE)
                 /\ network' = [network EXCEPT ![PRODUCER] = Append((network)[PRODUCER], value1)]
                 /\ pc' = [pc EXCEPT ![self] = "c2"]
            /\ UNCHANGED << processor, stream, requester >>

c2(self) == /\ pc[self] = "c2"
            /\ (Len((network)[self])) > (0)
            /\ LET msg00 == Head((network)[self]) IN
                 /\ network' = [network EXCEPT ![self] = Tail((network)[self])]
                 /\ LET yielded_network1 == msg00 IN
                      /\ processor' = yielded_network1
                      /\ pc' = [pc EXCEPT ![self] = "c"]
            /\ UNCHANGED << stream, requester >>

Consumer(self) == c(self) \/ c1(self) \/ c2(self)

p(self) == /\ pc[self] = "p"
           /\ IF TRUE
                 THEN /\ pc' = [pc EXCEPT ![self] = "p1"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << network, processor, stream, requester >>

p1(self) == /\ pc[self] = "p1"
            /\ (Len((network)[self])) > (0)
            /\ LET msg10 == Head((network)[self]) IN
                 /\ network' = [network EXCEPT ![self] = Tail((network)[self])]
                 /\ LET yielded_network00 == msg10 IN
                      /\ requester' = [requester EXCEPT ![self] = yielded_network00]
                      /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << processor, stream >>

p2(self) == /\ pc[self] = "p2"
            /\ stream' = ((stream) + (1)) % (BUFFER_SIZE)
            /\ LET yielded_stream0 == stream' IN
                 LET value00 == yielded_stream0 IN
                   /\ (Len((network)[requester[self]])) < (BUFFER_SIZE)
                   /\ network' = [network EXCEPT ![requester[self]] = Append((network)[requester[self]], value00)]
                   /\ pc' = [pc EXCEPT ![self] = "p"]
            /\ UNCHANGED << processor, requester >>

Producer(self) == p(self) \/ p1(self) \/ p2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in (1) .. (NUM_CONSUMERS): Consumer(self))
           \/ (\E self \in {PRODUCER}: Producer(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in (1) .. (NUM_CONSUMERS) : WF_vars(Consumer(self))
        /\ \A self \in {PRODUCER} : WF_vars(Producer(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION TLA-3b32e33f9317d9065792b6369f21a56b

ConsumerAlwaysConsumes ==
    \A self \in 1 .. NUM_CONSUMERS :
        pc[self] = "c1" ~> pc[self] = "c2"

=============================================================================
\* Modification History
\* Last modified Fri Dec 18 02:02:58 PST 2020 by finn
\* Last modified Mon Apr 01 02:11:17 PDT 2019 by minh
\* Last modified Tue Jan 22 18:38:13 PST 2019 by rmc
\* Last modified Wed Oct 12 02:41:48 PDT 2011 by lamport
\* Created Mon Oct 10 06:26:47 PDT 2011 by lamport
