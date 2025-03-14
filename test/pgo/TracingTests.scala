package pgo

import pgo.util.TLC
import os.makeDir.all
import scala.concurrent.duration.{MINUTES, Duration}

class TracingTests extends munit.FunSuite:
  override val munitTimeout = Duration(30, MINUTES)
  private val systemsDir = os.pwd / "systems"

  test("harvest systems/dqueue"):
    testHarvest(systemsDir / "dqueue")("go", "test")

  test("harvest systems/locksvc"):
    testHarvest(systemsDir / "locksvc")("go", "test", "-run", "Test5Clients")

  test("harvest systems/raftkvs (1)"):
    testHarvest(systemsDir / "raftkvs", tracesSubFolder = "traces_found_1")(
      "go",
      "test",
      "-run",
      "TestSafety_OneServer",
    )

  test("harvest systems/raftkvs (3)"):
    testHarvest(systemsDir / "raftkvs", tracesSubFolder = "traces_found_3")(
      "go",
      "test",
      "-run",
      "TestSafety_ThreeServers",
    )

  private def testHarvest(
      path: os.Path,
      tracesSubFolder: String = "traces_found",
  )(cmd: String*): Unit =
    pgo.PGo.main(
      Array(
        "harvest-traces",
        "--traces-needed",
        "0",
        "--traces-sub-folder",
        tracesSubFolder,
        path.toString,
        "--",
      ) ++ cmd,
    )

  private def testValidate(
      path: os.Path,
      tracesFolder: os.SubPath,
      cfgFragmentSuffix: String = "",
      allPaths: Boolean = true,
      validateName: String = "validate.out",
  ): Unit =
    val modelName = path.last
    val traceFile = path / s"$modelName.tla"
    val mpcalCmdParts = Seq("pcalgen", traceFile.toString)
    println(s"$$ pgo ${mpcalCmdParts.mkString(" ")}")
    pgo.PGo.main(mpcalCmdParts.toArray)

    // This is built in now
    // TLC.translatePCal(cwd = path, specFile = traceFile)

    val tracesDir = path / tracesFolder
    val cmdParts: os.Shellable =
      Seq[os.Shellable](
        "tracegen",
        traceFile.toString,
        tracesDir.toString,
        if cfgFragmentSuffix.nonEmpty then
          List("--cfg-fragment-suffix", cfgFragmentSuffix)
        else Nil,
        if allPaths then None else Some("--noall-paths"),
      )
    println(s"$$ pgo ${cmdParts.value.mkString(" ")}")
    pgo.PGo.main(cmdParts.value.toArray)

    TLC.runTLC(
      cwd = tracesDir,
      javaOpts = List("-Dtlc2.tool.queue.IStateQueue=StateDeque"),
      outFile = Some(tracesDir / validateName),
    )(s"${modelName}Validate.tla")

  private enum IgnoreToggle:
    case Yes, No

    def asBool: Boolean =
      this match
        case Yes => true
        case No  => false
  end IgnoreToggle
  private object IgnoreToggle:
    def apply(bool: Boolean): IgnoreToggle =
      if bool then IgnoreToggle.Yes else IgnoreToggle.No

    given default: IgnoreToggle = IgnoreToggle.No

    def setIgnore[T](bool: Boolean)(fn: IgnoreToggle ?=> T): T =
      fn(using IgnoreToggle(bool))
  end IgnoreToggle

  private def testTracesFolder(
      systemFolder: os.Path,
      tracesFolder: os.SubPath,
      cfgFragmentSuffix: String = "",
      allPaths: Boolean = true,
  )(using munit.Location, IgnoreToggle): Unit =
    os.list(systemFolder / tracesFolder)
      .foreach: tracesDir =>
        val name = s"validate $systemFolder $tracesFolder/${tracesDir.last}"
        test(
          if summon[IgnoreToggle].asBool then name.ignore
          else (name: munit.TestOptions),
        ):
          testValidate(
            path = systemFolder,
            tracesFolder = tracesDir.subRelativeTo(systemFolder),
            cfgFragmentSuffix = cfgFragmentSuffix,
            allPaths = allPaths,
          )

  testTracesFolder(systemsDir / "dqueue", os.sub / "traces_found")
  testTracesFolder(systemsDir / "locksvc", os.sub / "traces_found")

  // Too slow for CI, use to generate validation results for raftkvs
  IgnoreToggle.setIgnore(true):
    testTracesFolder(
      systemsDir / "raftkvs",
      os.sub / "traces_found_1",
      cfgFragmentSuffix = "1",
      allPaths = false,
    )
    testTracesFolder(
      systemsDir / "raftkvs",
      os.sub / "traces_found_2",
      cfgFragmentSuffix = "2",
      allPaths = false,
    )
    testTracesFolder(
      systemsDir / "raftkvs",
      os.sub / "traces_found_3",
      cfgFragmentSuffix = "3",
      allPaths = false,
    )
    testTracesFolder(
      systemsDir / "raftkvs",
      os.sub / "traces_found_3_fail",
      cfgFragmentSuffix = "3",
      allPaths = false,
    )
    testTracesFolder(
      systemsDir / "raftkvs",
      os.sub / "traces_found_4",
      cfgFragmentSuffix = "4",
      allPaths = false,
    )
    testTracesFolder(
      systemsDir / "raftkvs",
      os.sub / "traces_found_5",
      cfgFragmentSuffix = "5",
      allPaths = false,
    )
