package pgo.tracing

import scala.collection.mutable
import scala.concurrent.duration
import java.util.concurrent.TimeUnit

object HarvestTraces:
  private def toGoTimeStr(dur: duration.Duration): String =
    dur.unit match
      case TimeUnit.NANOSECONDS  => s"${dur.length}ns"
      case TimeUnit.HOURS        => s"${dur.length}h"
      case TimeUnit.MILLISECONDS => s"${dur.length}ms"
      case TimeUnit.MINUTES      => s"${dur.length}m"
      case TimeUnit.SECONDS      => s"${dur.length}s"
      case TimeUnit.MICROSECONDS | TimeUnit.DAYS =>
        throw IllegalArgumentException(s"unit ${dur.unit} not supported")

  private def readTraceCollection(folder: os.Path): Set[String] =
    os.list(folder)
      .filter(_.last.endsWith(".log"))
      .map(os.read)
      .toSet

  def apply(
      folder: os.Path,
      tracesSubFolderName: String,
      durations: List[duration.Duration],
      rediscoveryThreshold: Int,
      victimCmd: List[String]
  ): Unit =
    require(durations.nonEmpty)
    val tmpDir = os.temp.dir()
    val proc = os.proc(victimCmd)

    os.copy(
      from = folder,
      to = tmpDir,
      replaceExisting = true,
      mergeFolders = true
    )

    // This is a hack that makes the problem of running this with local PGo build "go away"
    if os.exists(tmpDir / "go.mod")
    then
      val modContents = os.read(tmpDir / "go.mod")
      val specialReplace =
        s"replace github.com/UBC-NSS/pgo/distsys => ${os.pwd / "distsys"}"
      val fixedModContents = modContents.replace(
        "replace github.com/UBC-NSS/pgo/distsys => ../../distsys",
        specialReplace
      )
      os.write.over(target = tmpDir / "go.mod", data = fixedModContents)
    end if

    val tracesSubFolder = folder / tracesSubFolderName
    os.makeDir.all(folder / tracesSubFolderName)
    val tracesSeen = mutable.HashMap[Set[String], os.Path]()
    os.list(tracesSubFolder)
      .filter(os.isDir)
      .foreach: dir =>
        val coll = readTraceCollection(dir)
        assert(
          !tracesSeen.contains(coll),
          s"$dir and ${tracesSeen(coll)} should not have the same contents"
        )
        tracesSeen.update(coll, dir)

    durations.foreach: disruptionRange =>
      println(
        s"looking for traces using max timeout $disruptionRange, rediscovery threshold = $rediscoveryThreshold..."
      )
      var uninterruptedUniqueTracesFound = 0
      while uninterruptedUniqueTracesFound < rediscoveryThreshold do
        val traceDir = os.temp.dir(dir = tmpDir)
        val result = proc.call(
          cwd = tmpDir,
          env = Map(
            "PGO_DISRUPT_CONCURRENCY" -> toGoTimeStr(disruptionRange),
            "PGO_TRACE_DIR" -> traceDir.toString
          ),
          mergeErrIntoOut = true,
          stdout = os.Inherit
        )
        val traces = readTraceCollection(traceDir)

        tracesSeen.get(traces) match
          case None =>
            val keepDir = os.temp.dir(tracesSubFolder, deleteOnExit = false)
            os.copy(
              from = traceDir,
              to = keepDir,
              replaceExisting = true,
              mergeFolders = true
            )
            tracesSeen.update(traces, keepDir)
            uninterruptedUniqueTracesFound = 0
            println(s"found new trace: $keepDir")
          case Some(existingDir) =>
            uninterruptedUniqueTracesFound += 1
            println(s"rediscovered existing trace: $existingDir")
      end while
      println(s"reached rediscovery threshold of $rediscoveryThreshold traces.")
    println(s"search finished for all max timeouts given.")
