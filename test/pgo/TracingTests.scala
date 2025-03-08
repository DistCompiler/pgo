package pgo

import org.scalatest.funsuite.AnyFunSuite
import pgo.util.TLC

class TracingTests extends AnyFunSuite:
  private val systemsDir = os.pwd / "systems"

  test("harvest systems/dqueue"):
    testHarvest(systemsDir / "dqueue")("go", "test")

  test("harvest systems/locksvc"):
    testHarvest(systemsDir / "locksvc")("go", "test", "-run", "Test5Clients")

  test("harvest systems/raftkvs"):
    testHarvest(systemsDir / "raftkvs")(
      "go",
      "test",
      "-run",
      "TestSafety_ThreeServers",
    )

  private def testHarvest(path: os.Path)(cmd: String*): Unit =
    pgo.PGo.main(Array("harvest-traces", path.toString, "--") ++ cmd)

  private def testValidate(path: os.Path)(folders: String*): Unit =
    val modelName = path.last
    val traceFile = path / s"$modelName.tla"
    val mpcalCmdParts = Seq("pcalgen", "--spec-file", traceFile.toString)
    println(s"$$ pgo ${mpcalCmdParts.mkString(" ")}")
    pgo.PGo.main(mpcalCmdParts.toArray)

    TLC.translatePCal(cwd = path, specFile = traceFile)

    folders.foreach: folder =>
      val tracesDir = path / "traces_found" / folder
      val cmdParts =
        Seq("tracegen", traceFile.toString, "--dest-dir", tracesDir.toString)
      println(s"$$ pgo ${cmdParts.mkString(" ")}")
      pgo.PGo.main(cmdParts.toArray)

      TLC.runTLC(cwd = tracesDir)(s"${modelName}Validate.tla")

  test("validate systems/dqueue"):
    testValidate(systemsDir / "dqueue")(
      "4161323826586722756",
      "5108295730686129910",
    )

  test("validate systems/locksvc"):
    testValidate(systemsDir / "locksvc")(
      "6466571574451277625",
      "18094128110711941820",
    )

  test("validate systems/raftkvs"):
    testValidate(systemsDir / "raftkvs")(
      // "14093705186468779628",
    )
