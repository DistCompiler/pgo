
def withPrefix(prefix: String)(assigns: String*): Seq[String] =
  assigns.map(assign => s"$prefix.$assign")

val aConsumerDefns = withPrefix("AConsumer")(
  "net=mapping:network",
  "proc=global:processor",
)

val aProducerDefns = withPrefix("AProducer")(
  "net=mapping:network",
  "requester=local:requester",
  "s=mapping:stream",
)

os.proc(
  "scala-cli",
  "run",
  ".",
  "--main-class",
  "pgo.PGo",
  "--",
  "pcalgen",
  "--spec-file",
  os.pwd / "tmp" / "dqueue.tla"
).call(
  cwd = os.pwd,
  mergeErrIntoOut = true,
  stdout = os.Inherit
)

val proc =
  os.proc(
    "scala-cli",
    "run",
    ".",
    "--main-class",
    "pgo.PGo",
    "--",
    "tracegen",
    "-d",
    "tmp/",
    "--model-name",
    "dqueue",
    "--trace-files",
    os.list(os.pwd / "systems" / "dqueue").filter(_.ext == "log"),
    "--mpcal-variable-defns",
    aConsumerDefns,
    aProducerDefns,
    "--mpcal-state-vars",
    "stream",
    "network",
    "--mpcal-constant-defns",
    "BUFFER_SIZE=99",
    "NUM_CONSUMERS=1",
    "NUM_PRODUCERS=1",
    "PRODUCER=0",
    //"--model-values",
  )

println(proc.commandChunks.mkString(" "))

val result = proc.call(cwd = os.pwd, check = false, mergeErrIntoOut = true)

if result.exitCode == 0
then println("generated ok")
else result.out.lines().foreach(println)
