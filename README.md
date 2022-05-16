# PGo ![CI Status](https://github.com/UBC-NSS/pgo/actions/workflows/ci.yml/badge.svg?branch=master)

PGo is a source to source compiler that translates Modular PlusCal
specifications (which use a superset of
[PlusCal](http://lamport.azurewebsites.net/tla/pluscal.html)) into [Go](https://golang.org/) programs.

In addition to the PGo compiler, this source tree includes:

- the `distsys` support library, which is used by PGo's generated Go code, available in the `distsys/` folder.
- syntax highlighting modes for Visual Studio Code and pygments, available in the `syntax/` folder.

We also made a [video that explains PGo](https://www.youtube.com/watch?v=H6-dQQSikik).

## Purpose and motivation

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
specification written in Modular PlusCal. The "Modular" prefix
comes from the need to distinguish the description of a system from
the model of its environment, which is needed for model checking.
PGo enables the translation of a Modular PlusCal description of a
distributed system to verifiable PlusCal,
as well as to a semantically equivalent Go program.

## Current status

Actively under development. PGo supports compilation of all PlusCal
control flow constructs.
PGo also supports a vast majority of the value-level TLA+ supported by TLC.
See the pull requests and issues for documentation of ongoing work.

In its active-development state, we do not provide stable releases.
To run PGo, the best way is to clone the repository, and, on the master branch, run it via the [sbt](https://www.scala-sbt.org/) build tool:
```
$ sbt
> run [command-line arguments]
```

See the usage notes below for what arguments the program accepts.

See [`manual.pdf`](https://github.com/UBC-NSS/pgo/blob/master/manual.pdf) (WARNING: update in progress) in the
repository for a snapshot of the latest version of the manual that details
implemented features and several examples.

## Usage

To learn how to use PGo during verification, see the [PGo usage page](https://github.com/UBC-NSS/pgo/wiki/PGo-Usage) (WARNING: update in progress).

For an in-depth description of how PGo works and how to interact with its generated code, see the manual (WARNING: update in progress).

For the tool's compilation modes and flags at a high level, see below.

The PGo tool's help text reads:

```
PGo compiler
  -h, --help   Show help message

Subcommand: gogen
  -o, --out-file  <arg>
  -p, --package-name  <arg>
  -s, --spec-file  <arg>
  -h, --help                  Show help message

Subcommand: pcalgen
  -s, --spec-file  <arg>
  -h, --help               Show help message
```

### gogen

The `gogen` subcommand requests that PGo generate a Go file from an MPCal-containing TLA+ module.
Most customisation of this stage should be done by choosing specific parameters when calling the generated Go code,
so there are only a few options to consider.

- `--out-file` specifies the path to the Go output file, like `-o` in GCC.
- `--spec-file` specifies the path to the TLA+ input file
- `--package-name` allows customisation of the package name of the Go output file. This defaults to a sanitized version of the
  MPCal algorithm name.

### pcalgen

The `pcalgen` subcommand requests that PGo rewrite its MPCal-containing TLA+ input file,
such that it contains a PlusCal translation of the MPCal algorithm.
The only option, `--spec-file`, is the path to the spec file, which will be rewritten.

To insert the PlusCal translation, PGo will look for comments like, give or take whitespace:
```
\* BEGIN PLUSCAL TRANSLATION
... any number of lines may go here
\* END PLUSCAL TRANSLATION
```

If it cannot find one of both of these comments in that order, it will give up with an error message describing the problem,
and will not write any output.

## How it works

PGo is a source to source compiler written in Scala. It compiles specifications written in an extension of PlusCal,
called Modular PlusCal (see the [Modular PlusCal page](https://github.com/UBC-NSS/pgo/wiki/Modular-PlusCal) for more details),
to Go programs.

## How to build (for development)

PGo's Scala code builds via an [sbt](https://www.scala-sbt.org/) project, with its dependencies managed
by [Maven](https://maven.apache.org/).
PGo additionally provides a runtime support library for its generated Go code, which lives in the `distsys/`
subfolder. This Go code is a standard Go module, which can be imported via the URL https://github.com/UBC-NSS/pgo/distsys.

The main build script is the top-level [build.sbt](https://github.com/UBC-NSS/pgo/blob/master/build.sbt).
To build from terminal, run `sbt` in the root directory and use the standard commands provided by the sbt console.
These include `run <command-line args>` to (re-)compile and run PGo, and `test` to run all tests, including Go tests
(TODO: add runner for free-standing Go tests; that one, specifically, is missing).

The sbt build can also be auto-imported by the IntelliJ Scala plugin, as well as likely any other IDE with Scala support.

PGo's Scala code has managed dependencies on a small set of utility libraries:

- [scallop](https://github.com/scallop/scallop) for command-line argument parsing
- [scala-parser-combinators](https://github.com/scala/scala-parser-combinators) for the TLA+/PCal/MPCal parser
- [os-lib](https://github.com/com-lihaoyi/os-lib) for simplified file and process manipulation (process manipulation is used during tests)

PGo's test suites additionally depend on:

- the `go` executable. The tests will attempt to find this, probably on the `$PATH` or equivalent, via the JVM's default lookup process.
- [ScalaTest](https://www.scalatest.org/) as test framework
- [ScalaCheck](https://www.scalacheck.org/) for implementing fuzz tests
- [java-diff-utils](https://github.com/java-diff-utils/java-diff-utils) for generating diffs when tests compare big blocks of text

PGo's Go runtime library depends on:

- [immutable](https://github.com/benbjohnson/immutable) for efficient immutable implementations of lists and maps in the TLA+ data model.
  For example, creating a modified map with one different key-value pair should take constant time, rather than copy the
  entire existing structure.
- [multierr](https://github.com/uber-go/multierr) for combining errors.

PGo is tested using OpenJDK 1.11 through 1.16, and Go 1.13 through 1.16.
OpenJDK 1.11+ is needed because of standard API usage.
Go >=1.13 is needed because of [changes to the errors package in that version](https://blog.golang.org/go1.13-errors),
and, otherwise, Go >=1.11 is needed due to the use of Go modules.
