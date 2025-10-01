package pgo

class CLITests extends munit.FunSuite:
  val dqueueTLA = pgo.projectRoot / "systems" / "dqueue" / "dqueue.tla"
  test("tracegen with no log files in dir: errors returned"):
    val tmp = os.temp.dir()
    try
      val Nil = pgo.PGo.run(
        scala.collection.immutable.ArraySeq(
          "tracegen",
          dqueueTLA.toString,
          tmp.toString,
        ),
      )
      fail("didn't exit with config error")
    catch case PGo.ConfigExit(1) => () // intended

  test("tracegen with one empty log file: no errors"):
    val tmp = os.temp.dir()
    os.write(tmp / "foo.log", "")
    assertEquals(
      pgo.PGo.run(
        scala.collection.immutable.ArraySeq(
          "tracegen",
          dqueueTLA.toString,
          tmp.toString,
        ),
      ),
      Nil,
    )
end CLITests
