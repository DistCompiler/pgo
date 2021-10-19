---- MODULE MappingMacroRules ----
EXTENDS Sequences, FiniteSets, Integers

CONSTANTS NODE_SET, SERVER_SET, BUFFER_SIZE

(*
--mpcal MappingMacroRules {
mapping macro TCPChannel {
    read {
        await Len($variable.queue) > 0 /\ $variable.enabled;
        with (msg = Head($variable.queue)) {
            $variable.queue := Tail($variable.queue);
            yield msg;
        };
    }

    write {
        await Len($variable.queue) < BUFFER_SIZE /\ $variable.enabled;
        yield [queue |-> Append($variable.queue, $value), enabled |-> $variable.enabled];
    }
}

mapping macro NetworkToggle {
    read {
        yield $variable.enabled;
    }

    write {
        yield [queue |-> $variable.queue, enabled |-> $value];
    }
}

archetype AServer(ref net[_], ref netToggle[_]) {
    lbl: skip;
}

archetype OtherArchetype(notRef) {
    lbl: skip;
}

variables
    network = [id \in NODE_SET |-> [queue |-> <<>>, enabled |-> TRUE]];

fair process (Server \in SERVER_SET) == instance AServer(ref network[_], ref network[_])
    mapping network[_] via TCPChannel
    (*:: expectedError: MPCalMultipleMapping *) mapping network[_] via NetworkToggle;

fair process (Server2 \in SERVER_SET) == instance AServer(ref network[_], ref network[_])
    mapping @1[_] via TCPChannel
    (*:: expectedError: MPCalMultipleMapping *) mapping @1[_] via NetworkToggle;

fair process (Server3 \in SERVER_SET) == instance AServer(ref network[_], ref network[_])
    mapping @2[_] via TCPChannel
    (*:: expectedError: MPCalMultipleMapping *) mapping @2[_] via NetworkToggle;

fair process (Server4 \in SERVER_SET) == instance AServer(ref network[_], ref network[_])
    mapping @1[_] via TCPChannel
    mapping @2[_] via NetworkToggle;

fair process (Server5 \in SERVER_SET) == instance OtherArchetype("foo")
    mapping (*:: expectedError: MPCalMappingValueRefMismatchError *) @1[_] via TCPChannel;
}

*)

\* BEGIN TRANSLATION
====