# Instructions on how to work with OmniLink

This folder contains build definitions that automate most experiments.
For all commands, _run them from the repo root, not here_.
That's where `./mill` lives.

The build definitions are in `package.mill`, with dependencies on `util.mill` and `GitRepo.mill`.

Note: all system dependencies are installed by the Dockerfile inside `../.devcontainer`.
If you use devcontainers, it will "just work".
Otherwise, make sure you have the packages listed there installed, and consider running `./mill mill.tabcomplete/install` to get tab completions on build actions.
You will use them a lot.

Each evaluated system lives in one subfolder.
Currently, `setbench` and `wiredtiger` work.
Note that you will need separate permission to check out a private form of `setbench`.

## Data management

All data is stored in a local DuckDB database named `eval.duckdb`.
It is not committed to source control, and acts as a persistent cache for recorded executions and validation results.
You should not need to interact with it directly.

All traces are uniquely identified by their configuration and a sequence number.
The build files configure what the known run configurations are, as well as options like thread count and operation count.

Because it is highly situational, the number of traces you need is not written in any build files.
Instead, run
```
./mill omnilink.wiredtiger.release_11_3_1.defaultConfig.setExpectedTraceCount 15
```
to require 15 traces.
If you already have 15 traces and want more, increase the number.
To query how many traces you have, you can either use tab completion:
```
./mill omnilink.wiredtiger.release_11_3_1.defaultConfig.traces<tab>
```
... or you can make an explicit request (notice the `show`):
```
./mill show omnilink.wiredtiger.release_11_3_1.defaultConfig.expectedTraceCount
```
Note that the actual count reflects any and all traces you already have in a given configuration, even if you never gathered them or asked for them yourself (common when transferring DBs from other machines).

## I ran experiments on one machine and want to read them on another

*Don't try to copy `out/`.*
It will just lead to broken paths and frustration.

The `omnilink/eval.duckdb` is a self-contained record of everything you did, including traces and counterexamples.
Copy that into the target machines `omnilink/` dir and run the commands you need (like extracting counterexamples).

How to merge different `eval.duckdb` is an open question.
For best future proofing, add build configs rather than editing existing ones, because the same config name doing different things would be confusing.
The system is built so many contradictory configs / builds / etc can coexist under different names.

## Gather and validate traces

To get traces for `wiredtiger`, run `./mill omnilink.wiredtiger.__.gatherTrace`.
For `setbench`, it's `./mill omnilink.setbench.__.gatherTrace`.

Note: this will clone and build the right version of the system under test on first run.

To validate, do the same thing but with `validateTrace` in place of `gatherTrace`.

## I have a big machine and I want my validation results faster

Because OmniLink runs TLC on 1 CPU core, it is a good candidate for parallel execution.
Mill actually defaults to parallelism when running tasks, but for TLC in particular that's quite dangerous.
While it doesn't use all your cores, TLC can easily consume GBs of RAM.
Running ~10 instances in parallel is a guaranteed trip to SWAP land, and may completely freeze your machine (out of memory killer might not even work properly, if it's enabled at all).

If you have your system monitor open and are willing to do some tuning, try something like this:
```
TLC_CONCURRENCY=2 ./mill omnilink.wiredtiger.__.validateTrace
```
In this example, setting that environment variable tells the build we allow 2 copies of TLC to run at once.
Anecdotally, my machine with 50GB of RAM available could handle 8-way parallelism for WiredTiger validation.
That said, at risk of having to restart your machine, be careful, tune up gradually, and don't assume all TLC workloads are equal.
They are not.

## View counterexamples

To view counterexample traces, run `./mill omnilink.wiredtiger.__.counterExamples` (either keep the `__`, or note that different build configs exist, such as `develop1`).
This will produce a list of file paths ending in `.bin`, and populate the repository root with that list for easy access.

To view these counterexamples, none of the stock TLA+ tooling works very well, so OmniLink ships its own.
To run that tooling, the best way is to run this _on a machine with a display_ (not a Docker container, nor a remote server):
```
MILL_OUTPUT_DIR=$(pwd)/out2 ./mill traceview
```

We had some trouble with .jars, JVM versions and packaging.
I did some reading, and the invocation above will get all the Java flags right for JavaFX to work as intended.
The `MILL_OUTPUT` variable allows us to have a 2nd Mill process dedicated to launching TraceView, which you can keep running in a 2nd terminal away from your IDE / any other tasks you want to run.
It will create `out2/`, of course, containing all that setup's build state.

Once you have TraceView open, it offers a dropdown listing all `.bin` files in your project root.
Pick one, and it will display that counterexample's end states.
The tool is representing the entire failed model check's state space, starting at the point where TLC could not make progress.
Click on a state name to show it in the detail view below and explore its properties.

To add rows, "+1 Row".
Each row contains all possible actions at that depth
You will quickly notice an overwheling number of possibilities.
To help you deal with this, the detail view offers a `Focus` toggle which will exclude all conflicting actions at that level of the state space.
Using it repeatedly lets you inspect specific paths through the state space, along with all the data TLC was using.

While showing differences along trace sequences is more challenging when your sequence is a tree, TraceView marks all possible differences when in doubt.
If a value changed, it is marked with `~`.
If a value is new, it is marked with `+`.
If a value is gone, it is marked with `!`.
The difference display reacts to Focus and becomes more precise as you eliminate parts of the state space.

To diagnose why TLC could not make progress, look in the `__successors` field in the top-most states, and think about why the corresponding spec action could not apply.
Note that the same action may have been possible in multiple states.
To automatically expose all levels containing these stalled successors, click "Reveal stalled states".
