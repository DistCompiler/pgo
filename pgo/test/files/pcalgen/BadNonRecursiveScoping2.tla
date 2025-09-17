---- MODULE BadNonRecursiveScoping2 ----

Bar == (*:: expectedError+3: ParseFailureError *) Foo

Foo == 12

\* BEGIN TRANSLATION
====