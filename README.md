# PGo #

PGo is a source to source compiler to compile
[PlusCal](http://lamport.azurewebsites.net/tla/pluscal.html) into
[Go lang](https://golang.org/).

## Purpose/motivation

[PlusCal](http://lamport.azurewebsites.net/tla/pluscal.html) is a
language for specifying/modeling concurrent systems. It was designed
to make it easier to write [TLA+](https://github.com/tlaplus). In
particular, PlusCal can be compiled into TLA+, which can be checked
against useful system properties (using the TLC model checker). For
example, [here](https://github.com/duerrfk/skp) is a repository of
PlusCal formulations of solutions to the mutual exclusion problem.

[Go](https://golang.org/) is a C based language developed by Google
for building distributed systems. It has built in support for
concurrency with channels, and goroutines, which makes it great for
developing distributed systems.

Currently there are no tools that correspond a PlusCal/TLA+ spec with
an implementation of the spec. PGo is a tool that aims to connect the
specification with the implementation by generating Go code based on a
PlusCal specification. PGo enables the translation of a verified
PlusCal specification of a distributed system algorithm into a
semantically equivalent Go program.

## Current status

Actively under development. PGo supports compilation of most
uni-process and very simple multiprocess PlusCal algorithms into
corresponding compilable and runnable Go code.

See `manual.pdf` in the repository for a snapshot of the latest version
of the manual that details implemented features and several examples.

## How does it work

PGo is a source to source compiler written in Java. It uses TLA+
toolset to parse PlusCal into an AST, which is then translated to a Go
AST, and finally written to a .go file.

## How do install it?

Requirements: JRE8, and one of Eclipse or Ant 1.9

1. First download/clone the repository

2. Option 1: Import as an Eclipse project
Option 2: Execute `ant pgo` assuming the project is in the `pgo/` directory

## How to Run

Run with eclipse. Arguments `-h` for help.
Alternatively, run the compiler with `./pgo.sh`.

## For Developers

If you use Eclipse, you should import the code style found in the
`pgo-code-style.epf` file by clicking `File -> Import...` and
selecting the file.

Furthermore, use the Unix text file line delimiter (especially
important if you are using Windows) by going to Eclipse's
preferences/options, and under General and Workspace set "New text
file line delimiter" to be "Unix".

By default Eclipse does not enable assertions. Our projects assume
that you have assertions enabled at all times.  To globally enable
assertions as a default for all projects, go to Window -> Preferences
-> Java / Installed JREs.  Select the JRE and click "Edit...". In the
"Default VM arguments" field, add "-ea"

## Usage Documentation

For more details, see `manual.pdf` in the repository.

### PlusCal annotations

Users can specify annotations in the PlusCal file to aid PGo in
compiling PlusCal to Go. Annotations are not location sensitive, but
they must appear within the `(* ... *)` for the PlusCal algorithm in
the TLA file.

Annotations appear in the PlusCal code within PlusCal comments, either `(* ... *)` or `\* ...`.
Each annotation is of the form `@PGo{ <annotation> }@PGo`. Multiple annotations of these formats can appear per comment.

#### TLA+ definitions and constants declared outside of the algorithm block (Required)

The PlusCal algorithm can make use of TLA+ definitions that are found
outside the algorithm block. These are not parsed by PGo and need to
be in an annotation for PGo to parse them.  The annotation for a TLA+
definition is of the form `def <name>(<params>)? <type>? == <TLA
expression>`.  The definition can be copied almost verbatim from the
TLA+, but a parameter is specified by `<name> <type>` so typing
information needs to be added to the parameters.  The type that the
expression should evaluate to may also be specified, if desired.  A
TLA+ definition without parameters is compiled into a variable, and a
definition with parameters is compiled into a function.

There will be constants in PlusCal that are not declared in the
PlusCal algorithm (e.g., constant N for model checking). These
variables will need to be specified using PGo annotations either as
constants of the Go program, or command line arguments of the Go
program.  Constants are specified as `const <varname> <type> <val>`
indicating that `varname` is a Go constant of type <type> with initial
value <val>.  Command line argument variables of Go are specified as
`arg <varname> <type> (<flagname>)?` indicating that variable
<varname> is of type <type> and is going to be specified through a
command line argument to the Go program. If no <flagname> is
specified, then the variable will be a positional argument in the
order that it appeared in the annotation. If <flagname> is specified,
then the variable will be set on the command line through
`-<flagname>=<value>`.

If a constant is not a primitive type, it cannot be declared as
constant or as a command line argument in Go. The constant can instead
be annotated as a TLA+ definition, where the expression is the desired
constant value. This will be compiled to a global variable that is
initialized with the given value. PGo provides a compile-time
guarantee that the constant indeed remains constant (it is not
assigned to or mutated).

#### Annotations for PlusCal procedure return values (Optional)

PlusCal has no return values, so procedures can only return values by
writing to a global variable. It is required to indicate which
variable serves this purpose. This is specified through the annotation
`ret <varname>`.  PGo automatically scans all function definitions for
the one where the variable is used.  Note that using this feature will
remove the specified variable from the global variables. If you rely
on global state of the variable for more than just the function return
value, do not specify it as a return value and use the global variable
instead.

#### Annotations for specifying variable types

PGo will automatically infer types for variables declared in
PlusCal. However, you may want to specify the types rather than using
the inferred types (e.g., you want a uint64 rather than int). This is
possible by specifying `var <varname> <type>`.  Type annotations are
required for variables that involve PlusCal tuples, since these may
compile to slices or tuples depending on context. If no type
annotation is provided for a variable, PGo will indicate the type it
inferred in the output Go code.

#### Annotations for specifying function types

Similar to specifying variable types. `func (<rtype>)? <funcname>()
<p1type>?+` represents <funcname>() having a return type of <rtype> if
specified, and parameters of type <p1type>, <p2type>... If any types
are specified, all return types or parameters must be specified.
