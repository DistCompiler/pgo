# PGo #

## Purpose/motivation

TLA+ is a specification language for distributed systems. Coupled with a TLC model checker, TLA+ allows for verification of distributed systems and algorithms. PlusCal is a C-syntax based language that allows for easier writing of TLA+, which is written in set and mathematical notation. https://github.com/tlaplus

Go is a C based language developed by Google for developing distributed systems. Go has built in support for concurrency with channels, and goroutines, which makes it very practical for developing distributed systems.

Currently there are no tools that corresponds TLA+ specification with the Go implementation of the same algorithm. PGo is a tool that aims to connect the specification with the implementation through allowing the generation of Go code based on a PlusCal specification. PGo would allow developers to translate a verified PlusCal specification of a distributed system algorithm into a valid Go program.

## Current status

Under development. 

## How does it work

PGo acts as a source to source compiler written in Java. It uses TLA+ toolset to parse PlusCal into an AST, which is then translated to a Go AST, and finally written.

## How do install it?

Requirements: JRE8, and one of Eclipse or Ant 1.9

1. First download the source

2. Option 1: Import as an Eclipse project
Option 2: Execute `ant pgo` assuming the project is in the `pgo/` directory

## How to Run

Run with eclipse. Arguments `-h` for help.
Alternatively, run `./pgo.sh` to execute the program.

## Usage Documentation
### PlusCal annotations
Users can specify annotations in the pluscal file to aid PGo in compiling PlusCal to Go.
PGo requires all variables used that is not defined in the PlusCal algorithm (e.g. constant N).

Annotations appear in the PlusCal code within PlusCal comments, either `(* ... *)` or `\* ...`.
Each annotation is of the form `@PGo{ <annotation> }@PGo`. Multiple annotations of these formats can appear per comment.
#### Annotation for undeclared PlusCal variables (Required)
There will be constants in PlusCal that are not declared in the PlusCal algorithm (e.g. constant N for model checking). These variables will need to be specified using PGo annotations either as constants of the Go program, or command line arguments of the Go program.
Constants are specified as `const <type> <varname> <val>` indicating that varname is a go constant of type <type> with initial value <val>.
Command line argument variables of Go are specified as `arg <type> <varname> (<flagname>)?` indicating that variable <varname> of type <type> and is going to be specified through command line argument to the go program. If no <flagname> is specified, then the variable will be positional arguments, the ith argument in the order they appear in the annotation. If <flagname> is specified, then the variable will be set through `-<flagname>=...`.

#### Annotations for PlusCal procedure return values (Optional)
PlusCal has no return values, so procedures can only return values by writing to a global variable. It is required to indicate which variable serves this purpose. This is specified through the annotation `ret <varname>`.
Note that using this feature will remove the specified variable from global variables. If you rely on global state of the variable for more than just function return value, do not specify it as a return value.

#### Annotations for specifying variable types
PGo will automatically infer types for variables declared in PlusCal. However, you may want to specify the types rather than using the inferred types (e.g. you want a uint64 rather than int). This is possible by specifying `var <type> <varname>`.

#### Annotations for specifying function types
Similar to specifying variable types. `func (<rtype>)? <funcname>() <p1type>?+` represents <funcname>() having a return type of <rtype> if specified, and parameters of type <p1type>, <p2type>... If you specify any types of function, all return types or parameters must be specified.
Note: macro functions will automatically have the parameters as pointers of the type you specified.

#### Annotations for specifying process ID type
All processes must have an ID of some sort. In PlusCal, processes are written as `process(Var \in Set)` or `process(Var = <val>)`. Var will be used as the ID of the process. The type of var must be specified as `proc <type> Var`.
