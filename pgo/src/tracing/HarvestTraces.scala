package pgo.tracing

import java.util.concurrent.TimeUnit

import scala.collection.mutable
import scala.concurrent.duration
import scala.concurrent.duration.Duration

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
      tracesNeeded: Int,
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

    val workspaceRoot = System.getenv("MILL_WORKSPACE_ROOT") match
      case null => os.pwd
      case path => os.Path(path, os.pwd)

    // Add a go.work that resolves the library module relative to the dev checkout
    if os.exists(tmpDir / "go.mod")
    then
      os.write.over(
        tmpDir / "go.work",
        s"""go 1.24.0
           |
           |use ${workspaceRoot / "distsys"}
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
      s"looking for traces using disruption time $disruptionTime, unique traces needed = $tracesNeeded...",
    )
    var uniqueTracesFound = 0
    var firstRun = true
    while uniqueTracesFound < tracesNeeded || firstRun do
      firstRun = false

      val keepDir = os.temp.dir(tracesSubFolder, deleteOnExit = false)
      val result = proc.call(
        cwd = tmpDir,
        env = Map(
          "PGO_DISRUPT_CONCURRENCY" -> toGoTimeStr(disruptionTime),
          "PGO_TRACE_DIR" -> keepDir.toString,
        ),
        mergeErrIntoOut = true,
        stdout = os.Inherit,
        check = false,
        timeout = Duration(1, TimeUnit.MINUTES).toMillis,
      )
      if result.exitCode != 0
      then println(s"!!! exit code ${result.exitCode}")

      val traces = readTraceCollection(keepDir)

      tracesSeen.get(traces) match
        case None =>
          tracesSeen.update(traces, keepDir)
          uniqueTracesFound += 1
          println(s"found new trace: $keepDir")
        case Some(existingDir) =>
          println(s"rediscovered existing trace: $existingDir")
          os.remove.all(keepDir)
    end while
    println(s"reached discovery threshold of $tracesNeeded unique traces.")
