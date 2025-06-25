# PGo <img src="piggo.svg" alt="PGo logo" style="width: 1em; height: 1em; vertical-align: middle" /> ![CI Status](https://github.com/DistCompiler/pgo/actions/workflows/ci.yml/badge.svg?branch=main)

[PGo](https://distcompiler.github.io/) is a source to source compiler that translates Modular PlusCal
specifications (which use a superset of
[PlusCal](http://lamport.azurewebsites.net/tla/pluscal.html)) into [Go](https://golang.org/) programs.

In addition to the PGo compiler, this source tree includes:

- the `distsys` support library, which is used by PGo's generated Go code, available in the `distsys/` folder.
- systems built using PGo in the `systems/` folder, including a Raft-based key-value store.
- syntax highlighting modes for Visual Studio Code and pygments, available in the `syntax/` folder.
- the TraceLink utility, for validating MPCal models against implementation execution traces.

You can read more about the research aspects of our work in our [ASPLOS'23 paper](https://doi.org/10.1145/3575693.3575695), a copy of which is [included in this repository](doc/papers/asplosb23main-p12-p-e73de3693c-62943-final.pdf).
Our evaluation of PGo distinguished artifact award at that conference 🏆.

We also have a couple of videos you can watch:
- [PGo TLA+ conference talk, September 2022](https://www.youtube.com/watch?v=XHqd60ZeUBo)
- [PGo overview talk, February 2022](https://www.youtube.com/watch?v=H6-dQQSikik).

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

In its active-development state, we do not provide stable releases, but as an experiment, a recent snapshot of PGo is available from Maven as `com.fhackett:pgo::0.1.0`.

To run PGo, the best way is to clone the repository, and, on the main branch, run it via the bundled [mill](https://mill-build.org/mill/index.html) build tool:
```
./mill pgo.runMain pgo.PGo --help
```
We also provide a helper script `./pgo.sh`, which acts like a development-local PGo executable.

To make your own local build, run the following:
```
./mill pgo.assembly
```
You can then find an executable file `out/pgo/assembly.dest/out.jar`, which is usable as a portable PGo executable.

See the usage notes below for what arguments the program accepts.

## Usage

To learn how to use PGo during verification, see the [PGo usage page](https://github.com/DistCompiler/pgo/wiki/PGo-Usage) (WARNING: this information needs updating).

For the tool's compilation modes and flags at a high level, see below.

The PGo tool's help text reads (with subcommand parts moved into each relevant section):

```
PGo compiler
  -n, --no-multiple-writes   whether to allow multiple assignments to the same
                             variable within the same critical section. PCal
                             does not. defaults to false.
  -h, --help                 Show help message

Subcommand: gogen
  ...
Subcommand: pcalgen
  ...
Subcommand: tracegen
  ...
Subcommand: tlc
  ...
```

### gogen

The `gogen` subcommand requests that PGo generate a Go file from an MPCal-containing TLA+ module.
Most customisation of this stage should be done by choosing specific parameters when calling the generated Go code,
so there are only a few options to consider.

```
  -o, --out-file  <arg>       the output .go file to write to.
  -p, --package-name  <arg>   the package name within the generated .go file.
                              defaults to a normalization of the MPCal block
                              name.
  -h, --help                  Show help message

 trailing arguments:
  spec-file (required)   the .tla specification to operate on.
```

### pcalgen

The `pcalgen` subcommand requests that PGo rewrite its MPCal-containing TLA+ input file,
such that it contains a PlusCal translation of the MPCal algorithm.
It requires the path to the spec file, which will be rewritten.

```
  -h, --help   Show help message

 trailing arguments:
  spec-file (required)   the .tla specification to operate on.
```

To insert the PlusCal translation, PGo will look for comments like, give or take whitespace:
```
\* BEGIN PLUSCAL TRANSLATION
... any number of lines may go here
\* END PLUSCAL TRANSLATION
```

If it cannot find one of both of these comments in that order, it will give up with an error message describing the problem,
and will not write any output.

## tracegen

Generate a tracing setup.
The requires arguments are the TLA+ specification and a directory, which is both where `.log` files generated by an instrumented PGo implementation live, and where the auxiliary TLA+ files for trace validation will be generated.

You can customize whether TLC should follow all paths or just one, a `.cfg` file including manual TLC configuration, whether to generate progress-inv ("sidestep" in the paper), and whether to prune paths by reasoning about physical time.

```
  -a, --all-paths                    explore all paths (as opposed to just one);
                                     default = true
      --noall-paths
  -c, --cfg-file  <arg>              config file fragment to include in
                                     *Validate.cfg
      --cfg-fragment-suffix  <arg>   suffix to add to
                                     {model_name}Validate{suffix}.cfg, when
                                     looking for a manual config file
  -l, --logs-dir  <arg>              directory containing log files to use
      --physical-clocks              rule out interleavings by reasoning about
                                     wall-clock time; default = false
      --nophysical-clocks
  -p, --progress-inv                 assert vector clock progress is always
                                     possible; default = true
      --noprogress-inv
  -h, --help                         Show help message

 trailing arguments:
  spec-file (required)   the specification file from which to infer parameters
  dest-dir (required)    directory into which code should be generated
```

## harvest-traces

Utility that helps re-run a PGo-generated system in order to gather unique sets of traces.
It should be invoked with tool-specific options, then `-- prog invocation`, a bit like the `time` command.
Note: it currently only works from the repository root, as it automatically splices a dependency on the local the `distsys` checkout into any `go.mod` files used by the target system.

It uses environment variables to configure the running Go code, and you can use any command-line invocation that runs the intended code once.

When collecting traces, it will stream them into the folder you specify, and then delete them if they turn out to be identical to another set that is present.

Additional options include how many unique traces you need, and the average disruption time to apply to the system.
Beware that, for very simple systems, requesting many traces might cause an endless loop due to a limited set of traces being possible.

```
  -d, --disruption-time  <arg>     average time for disruptions
      --traces-needed  <arg>       how many unique traces to discover
  -t, --traces-sub-folder  <arg>   subfolder to store generated traces
  -h, --help                       Show help message

 trailing arguments:
  folder (required)       folder where the system to trace lives
  victim-cmd (required)   command to launch the implementation code, specify
                          after -- (will be launched repeatedly)
```

## tlc

This is a helper to streamline the workflow of using TLC in tandem with TraceLink / PGo.
PGo packages a JAR file containing TLC and a compatible version of CommunityModules, and this command invokes it.
To talk to TLC and not PGo's argument parser, pass your arguments after `--`.

This command has a specific helper `--dfs`, which replaces setting the much longer and more complex Java property that switches TLC's state queue to a stack, causing it to search for states depth-first instead of depth-first.

```
  -d, --dfs     enable depth-first search
      --nodfs
  -h, --help    Show help message

 trailing arguments:
  tlc-args (required)   arguments to forward to TLC
```

## How it works

PGo is a source to source compiler written in Scala. It compiles specifications written in an extension of PlusCal,
called Modular PlusCal (see the [Modular PlusCal page](https://github.com/DistCompiler/pgo/wiki/Modular-PlusCal) for more details),
to Go programs.

## How to build (for development)

PGo's Scala code builds via [mill](https://mill-build.org/mill/index.html), which manages dependencies, Java versions, and so forth automatically.
PGo additionally provides a runtime support library for its generated Go code, which lives in the `distsys/`
subfolder, and builds with the Go toolchain.
This Go code is a standard Go module, which can be imported via the URL https://github.com/DistCompiler/pgo/distsys.

Build metadata is organized in [build.mill](https://github.com/DistCompiler/pgo/blob/main/build.mill).
See that file for all dependencies and their current versions.
A working Go installation is also needed to run the tests.
Version 1.24.0 is used by the devcontainer.
Note the difference between full dependencies and test-time dependencies, like the test framework we use.

To run all the tests, use the command `./mill pgo.test`.
It will handle the entire compile and run cycle.
This will automatically run the Go tests and PGo-generated system integration tests.

For any IDE with Scala Metals support, PGo's source should be auto-importable.

See `.github/workflows/ci.yml` for a list of Go and Java versions against which PGo is tested.
