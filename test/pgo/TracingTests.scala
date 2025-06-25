package pgo

import pgo.util.TLC
import os.makeDir.all
import scala.concurrent.duration.{MINUTES, Duration}

class TracingTests extends munit.FunSuite:
  override val munitTimeout = Duration(30, MINUTES)
  private val systemsDir = projectRoot / "systems"

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

  private def testHarvest(
      path: os.Path,
      tracesSubFolder: String = "traces_found",
  )(cmd: String*): Unit =
    val origContents = os.list(path / tracesSubFolder).filter(os.isDir).toSet
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
    val updatedContents = os.list(path / tracesSubFolder).filter(os.isDir).toSet

    (updatedContents -- origContents).foreach: addedDir =>
      println(s"rm spurious dir $addedDir")
      os.remove.all(addedDir)
  end testHarvest

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

  private def testTracesFolder(
      systemFolder: os.Path,
      tracesFolder: os.SubPath,
      cfgFragmentSuffix: String = "",
      allPaths: Boolean = true,
  )(using munit.Location): Unit =
    os.list(systemFolder / tracesFolder)
      .foreach: tracesDir =>
        val name = s"validate $systemFolder $tracesFolder/${tracesDir.last}"
        test(name: munit.TestOptions):
          testValidate(
            path = systemFolder,
            tracesFolder = tracesDir.subRelativeTo(systemFolder),
            cfgFragmentSuffix = cfgFragmentSuffix,
            allPaths = allPaths,
          )

  testTracesFolder(systemsDir / "dqueue", os.sub / "traces_found")
  testTracesFolder(systemsDir / "locksvc", os.sub / "traces_found")

  // At minimum, check that we can validate raftkvs for 1 node at least.
  // Bigger is too slow to be practical, so we leave that out.
  testTracesFolder(
    systemsDir / "raftkvs",
    os.sub / "traces_found_1",
    cfgFragmentSuffix = "1",
    allPaths = false,
  )
