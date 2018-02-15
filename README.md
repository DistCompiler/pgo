# This project has relocated to github: https://github.com/UBC-NSS/pgo #

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

## How to install it?

Requirements: Eclipse or Ant 1.9

1. First download/clone the repository

2. Option 1: Import as an Eclipse project
Option 2: Execute `ant pgo` assuming the project is in the `pgo/` directory

Dependencies:

- The [Plume options library](https://mernst.github.io/plume-lib/).

- The [TLA+ tools](https://github.com/tlaplus/tlaplus/tree/master/tlatools/src).

- The [Go Data Structures library](https://github.com/emirpasic/gods).

PGo was tested on JRE8 and Go 1.8.3.

## How to run

Run with eclipse. Arguments `-h` for help.
Alternatively, run the compiler with `./pgo.sh`.

## For developers

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

# This project has relocated to github: https://github.com/UBC-NSS/pgo #


