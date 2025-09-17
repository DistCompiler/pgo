---- MODULE BadNonRecursiveScoping1 ----

Foo == (*:: expectedError+3: ParseFailureError *) Foo

\* BEGIN TRANSLATION
====