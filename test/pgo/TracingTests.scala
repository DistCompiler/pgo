package pgo

import pgo.util.TLC
import os.makeDir.all
import scala.concurrent.duration.{HOURS, Duration}

class TracingTests extends munit.FunSuite:
  override val munitTimeout = Duration(1, HOURS)
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
      tracesSubFolder: String = "traces_found",
      cfgFragmentSuffix: String = "",
      allPaths: Boolean = true,
  )(folders: String*): Unit =
    val modelName = path.last
    val traceFile = path / s"$modelName.tla"
    val mpcalCmdParts = Seq("pcalgen", traceFile.toString)
    println(s"$$ pgo ${mpcalCmdParts.mkString(" ")}")
    pgo.PGo.main(mpcalCmdParts.toArray)

    // This is built in now
    // TLC.translatePCal(cwd = path, specFile = traceFile)

    folders.foreach: folder =>
      val tracesDir = path / tracesSubFolder / folder
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
      )(s"${modelName}Validate.tla")

  test("validate systems/dqueue"):
    testValidate(systemsDir / "dqueue")(
      "4161323826586722756",
      "5108295730686129910",
      "9784577860662347592",
    )

  test("validate systems/locksvc"):
    testValidate(systemsDir / "locksvc")(
      "6466571574451277625",
      "18094128110711941820",
      "10048212154511080998",
      "11574333657589578207",
      "1581616650049015642",
      "4034722711531820390",
      "5100904165634445979",
      "5328669688304715284",
      "5924614947138120035",
      "7279137884356440435",
      "8381260534786140194",
      "930541271391487742",
      "966904087995387682",
      "12611588159469363664",
      "1029352561734837753",
    )

  test("validate systems/raftkvs (1)"):
    testValidate(
      systemsDir / "raftkvs",
      tracesSubFolder = "traces_found_1",
      cfgFragmentSuffix = "1",
      allPaths = false,
    )(
      "3368450613225909642",
      "8151152544257240581",
      "13569289695856064955",
      "15553159120300775126",
      "17072238690596337743",
    )

  test("validate systems/raftkvs (3)"):
    testValidate(
      systemsDir / "raftkvs",
      tracesSubFolder = "traces_found_3",
      cfgFragmentSuffix = "3",
      allPaths = false,
    )(
      "1943712620049762309",
      "4829811417081991779",
      "5930104509848537098",
      "6933260783345230717",
      "12089597339614454083",
      "13681026299002763987",
    )
