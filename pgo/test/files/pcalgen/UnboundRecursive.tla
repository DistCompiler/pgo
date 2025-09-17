---- MODULE UnboundRecursive ----
EXTENDS TLC, Integers

RECURSIVE (*:: expectedError: UnboundRecursiveDeclError *) Foo(_, _)

\* BEGIN TRANSLATION
====