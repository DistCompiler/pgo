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
The build files configure how many traces are expected, and traces will be generated or loaded from the DB based on whether a record of that trace already exists.
To request more traces, look for `def configs` and the `tracesNeeded` field.

## Gather and validate traces

To get traces for `wiredtiger`, run `./mill omnilink.wiredtiger.__.gatherTrace`.
For `setbench`, it's `./mill omnilink.sebench.__.gatherTrace`.

To validate, do the same thing but with `validateTrace` in place of `gatherTrace`.

## View counterexamples

To view counterexample traces, run `./mill omnilink.wiredtiger.__.counterExamples` (either keep the `__`, or note that different build configs exist, such as `develop1`).
This will produce a list of file paths ending in `.bin`.

To view these counterexamples, none of the stock TLA+ tooling works very well, so OmniLink ships its own.
To build that tooling, run `./mill show traceview.assembly`.
It will print a path ending in `.jar`.
Copy that jar somewhere convenient, name it `traceview.jar`, and launch it as `./traceview.jar`.
Note: the dev container is not configured to forward the tool's GUI, so launch it outside your container if you have one.
The `traceview.jar` itself requires only a recent Java build, and should "just work" on almost any system.

TraceView is a simple app which loads one of those `.bin` files above via a file picker, and displays the logical trace computed by TLC.
The trace started _last event at the top_, since this is usually key evidence of what went wrong.
You can extend the view to include earlier events using the +/- buttons.

When reading event records, they are in the same format as TLC, but with some domain specific extensions.
Event names are used as headings, and there are special fields for debugging.
Added fields are marked `+` (green highlight), and changed fields are marked `>` (yellow highlight).
Most important is `__successors`, which maps process IDs to the next steps each process could have taken.
Often, there is just one process and one impossible next step.
Currently the process is to look at the last successful event (top of trace), check its successors, and manually think about why the TLA+ model does not consider that event valid in context.

Notice the "Load another trace" at the bottom of the UI.
It will open the file picker and reset the tool to view another trace.
