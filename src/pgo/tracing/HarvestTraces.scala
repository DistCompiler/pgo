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
      case TimeUnit.MICROSECONDS => s"${dur.length}us"
      case TimeUnit.DAYS =>
        throw IllegalArgumentException(s"unit ${dur.unit} not supported")

  private def readTraceCollection(folder: os.Path): Set[List[ujson.Value]] =
    os.list(folder)
      .filter(_.last.endsWith(".log"))
      .map: logFile =>
        val lines = os.read.lines(logFile)
        lines
          .map: line =>
            val obj = ujson.read(line)
            obj.obj -= "startTime"
            obj.obj -= "endTime"
            obj
          .toList
      .toSet

  def apply(
      folder: os.Path,
      tracesSubFolderName: String,
      disruptionTime: duration.Duration,
      rediscoveryThreshold: Int,
      victimCmd: List[String],
  ): Unit =
    val tmpDir = os.temp.dir()
    val proc = os.proc(victimCmd)

    os.copy(
      from = folder,
      to = tmpDir,
      replaceExisting = true,
      mergeFolders = true,
    )

    // Add a go.work that resolves the library module relative to the dev checkout
    if os.exists(tmpDir / "go.mod")
    then
      os.write.over(
        tmpDir / "go.work",
        s"""go 1.24.0
           |
           |use ${os.pwd / "distsys"}
           |use $tmpDir
           |""".stripMargin,
      )
    end if

    val tracesSubFolder = folder / tracesSubFolderName
    os.makeDir.all(folder / tracesSubFolderName)
    val tracesSeen = mutable.HashMap[Set[List[ujson.Value]], os.Path]()
    os.list(tracesSubFolder)
      .filter(os.isDir)
      .foreach: dir =>
        val coll = readTraceCollection(dir)
        assert(
          !tracesSeen.contains(coll),
          s"$dir and ${tracesSeen(coll)} should not have the same contents",
        )
        tracesSeen.update(coll, dir)

    println(
      s"looking for traces using disruption time $disruptionTime, rediscovery threshold = $rediscoveryThreshold...",
    )
    var firstRun = true
    var uninterruptedUniqueTracesFound = 0
    while uninterruptedUniqueTracesFound < rediscoveryThreshold || firstRun do
      firstRun = false
      val traceDir = os.temp.dir(dir = tmpDir)
      val result = proc.call(
        cwd = tmpDir,
        env = Map(
          "PGO_DISRUPT_CONCURRENCY" -> toGoTimeStr(disruptionTime),
          "PGO_TRACE_DIR" -> traceDir.toString,
        ),
        mergeErrIntoOut = true,
        stdout = os.Inherit,
      )
      val traces = readTraceCollection(traceDir)

      tracesSeen.get(traces) match
        case None =>
          val keepDir = os.temp.dir(tracesSubFolder, deleteOnExit = false)
          os.copy(
            from = traceDir,
            to = keepDir,
            replaceExisting = true,
            mergeFolders = true,
          )
          tracesSeen.update(traces, keepDir)
          uninterruptedUniqueTracesFound = 0
          println(s"found new trace: $keepDir")
        case Some(existingDir) =>
          uninterruptedUniqueTracesFound += 1
          println(s"rediscovered existing trace: $existingDir")
    end while
    println(s"reached rediscovery threshold of $rediscoveryThreshold traces.")
