---- MODULE bug2 ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS NUM_NODES, BUFFER_SIZE

(* --mpcal bug2 {
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

    archetype AEchoServer(ref net[_])
    variables
        msg;
    {
        serverLoop:
            while (TRUE) {
                rcvMsg:
                    msg := net[self, 1];
                sndMsg:
                    net[msg.from, msg.typ] := [from |-> self, to |-> msg.from,
                                              body |-> msg.body, typ |-> msg.typ];
            };
    }

    variables
        network = [id \in 1..NUM_NODES, typ \in 1..4 |-> <<>>];

    fair process (EchoServer \in 1..NUM_NODES) == instance AEchoServer(ref network[_])
        mapping network[_] via TCPChannel;
}

\* BEGIN PLUSCAL TRANSLATION

\* END PLUSCAL TRANSLATION
*)

\* BEGIN TRANSLATION
====