# How to Run PGo's Systems on Antithesis

Let's start with the simple version.

Make sure you have a similar setup to the Dockerfile in `../.devcontainer` (or just open this repo in a dev container).
Also make sure this folder contains the relevant Docker credentials in `mongoresearch.key.json`, as well as the correct username/password pair stored in `mongoresearch.user.txt` and `mongoresearch.password.txt` respectively.

**Disclaimer: this may embed URLs (but no credentials!) to my specific Antithesis testing account. Adapt or re-use at your own peril.**
I am sharing this sub-folder so the Antithesis team can see what I'm doing and help me with troubleshooting.

All Antithesis build scripting is done with the Mill build tool, and lives in `../antithesis.mill`.
It's basically just Scala code, but with dependency + output folder management and concurrency support.
Ctrl+click should work, and you can work backwards from the target names below to figure out how they work.
The `.` in a target name refers to nested `object` definitions.
Almost everything is "just" Li Haoyi's os-lib library, subprocesses, and file copying.
There is an effort to print when a subprocess is invoked, starting with `$` in the build log.

To launch `systems/dqeue`, run this from the repo root:
```
./mill antithesis.dqueue.runner.launch
```

To launch `systems/raftkvs`, run this from the repo root:
```
./mill antithesis.raftkvs.runner.launch
```

If the build gets stale, or you want to ensure there are no caching problems, run `./mill clean` and/or delete `/out`.

## How to locally test the Docker images

Relevant `docker-compose.yml` and `Dockerfile.*` files live in subfolders of this directory.
While the build uses a lot of generated folders to run and set up build context, the `docker-compose.yml` will work in place if you call it manually, assuming the images are built correctly.

For instance, here are commands to assemble the necessary Docker images (and incidentally to push them to Antithesis), and then run a test workload.

Build the images:
```
./mill show antithesis.raftkvs.runner.images
```
This will show a list of the image names, after building them and pushing them to Antithesis.

Launch the system:
```
cd antithesis/raftkvs
docker compose up
```

Run the client:
```
cd antithesis/raftkvs
docker compose exec -ti client1 /opt/antithesis/test/v1/quickstart/singleton_driver_random_workload.sh 
```

Run validation using TraceLink:
```
cd antithesis/raftkvs
docker compose exec -ti client1 /opt/antithesis/test/v1/quickstart/finally_tracelink.sh
```

Tear down the system (notice the `-v` to remove the volume, or you will leak log files between runs!):
```
cd antithesis/raftkvs
docker compose down -v
```

## How to enable / disable Antithesis instrumentation

The build is able to instrument PGo's generated Go code using Antithesis's instrumentor tool.
Trouble is, the instrumentor doesn't handle multiple modules right now.

To re-enable instrumentation, look for this in `../antithesis.mill`:
```scala
// Note: change `modNotInstrumented` to `mod` to include instrumentation
```
Do what the comment says, and the system will instrument 1 or more of the Go modules.
If you do that for more than one of the listed modules, the compiled system will crash on start-up with an assertion failure.
Instrument just one, then the problem should not apply, including packaging up the symbol data and including it in the relevant Docker image.

To just get to the generated build dir and play around with Go commands, do this:
```
./mill show antithesis.raftkvs.workspace
```

It will output a subdirectory of `../out/` containing a self-contained Go workspace, where this build runs its compile commands.
