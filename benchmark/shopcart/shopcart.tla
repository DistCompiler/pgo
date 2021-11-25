------------------------------- MODULE shopcart -------------------------------

\* do not check for deadlocks.

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT NumNodes

(********************

--mpcal shopcart {
    define {
        AddCmd == 1
        RemoveCmd == 2

        Elem1 == "elem1"
        Elem2 == "elem2"

        NodeSet == 1..NumNodes
    }

    mapping macro InputQueue {
        read {
            await Len($variable) > 0;
            with (r = Head($variable)) {
                $variable := Tail($variable);
                yield r;
            };
        }

        write {
            yield Append($variable, $value);
        }
    }

    archetype ANode(ref cart, ref in) {
    nodeLoop:
        while (TRUE) {
            with (req = in) {
                if (req.cmd = AddCmd) {
                    cart := cart \cup {req.elem};
                } else if (req.cmd = RemoveCmd) {
                    cart := cart \ {req.elem};
                };
            };
        };
    }

    variables
        cart = {},
        in = <<
            [cmd |-> AddCmd, elem |-> Elem1],
            [cmd |-> RemoveCmd, elem |-> Elem2],
            [cmd |-> AddCmd, elem |-> Elem2],
            [cmd |-> RemoveCmd, elem |-> Elem1]
        >>;
    
    fair process (node \in NodeSet) == instance ANode(ref cart, ref in)
        mapping in via InputQueue;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm shopcart {
  variables cart = {}; in = <<[cmd |-> AddCmd, elem |-> Elem1], [cmd |-> RemoveCmd, elem |-> Elem2], [cmd |-> AddCmd, elem |-> Elem2], [cmd |-> RemoveCmd, elem |-> Elem1]>>;
  define{
    AddCmd == 1
    RemoveCmd == 2
    Elem1 == "elem1"
    Elem2 == "elem2"
    NodeSet == (1) .. (NumNodes)
  }
  
  fair process (node \in NodeSet)
  {
    nodeLoop:
      if(TRUE) {
        await (Len(in)) > (0);
        with (r0 = Head(in)) {
          in := Tail(in);
          with (yielded_in = r0) {
            with (req = yielded_in) {
              if(((req).cmd) = (AddCmd)) {
                cart := (cart) \union ({(req).elem});
                goto nodeLoop;
              } else {
                if(((req).cmd) = (RemoveCmd)) {
                  cart := (cart) \ ({(req).elem});
                  goto nodeLoop;
                } else {
                  goto nodeLoop;
                };
              };
            };
          };
        };
      } else {
        goto Done;
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "c88a080" /\ chksum(tla) = "c622bac0")
VARIABLES cart, in, pc

(* define statement *)
AddCmd == 1
RemoveCmd == 2
Elem1 == "elem1"
Elem2 == "elem2"
NodeSet == (1) .. (NumNodes)


vars == << cart, in, pc >>

ProcSet == (NodeSet)

Init == (* Global variables *)
        /\ cart = {}
        /\ in = <<[cmd |-> AddCmd, elem |-> Elem1], [cmd |-> RemoveCmd, elem |-> Elem2], [cmd |-> AddCmd, elem |-> Elem2], [cmd |-> RemoveCmd, elem |-> Elem1]>>
        /\ pc = [self \in ProcSet |-> "nodeLoop"]

nodeLoop(self) == /\ pc[self] = "nodeLoop"
                  /\ IF TRUE
                        THEN /\ (Len(in)) > (0)
                             /\ LET r0 == Head(in) IN
                                  /\ in' = Tail(in)
                                  /\ LET yielded_in == r0 IN
                                       LET req == yielded_in IN
                                         IF ((req).cmd) = (AddCmd)
                                            THEN /\ cart' = ((cart) \union ({(req).elem}))
                                                 /\ pc' = [pc EXCEPT ![self] = "nodeLoop"]
                                            ELSE /\ IF ((req).cmd) = (RemoveCmd)
                                                       THEN /\ cart' = (cart) \ ({(req).elem})
                                                            /\ pc' = [pc EXCEPT ![self] = "nodeLoop"]
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "nodeLoop"]
                                                            /\ cart' = cart
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                             /\ UNCHANGED << cart, in >>

node(self) == nodeLoop(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in NodeSet: node(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in NodeSet : WF_vars(node(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* Properties

ValueOK == <>(cart = {Elem2})

=============================================================================
