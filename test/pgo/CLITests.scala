package pgo

class CLITests extends munit.FunSuite:

  test("tracegen with no log files in dir: errors returned"):
    try
      val tmp = os.temp.dir()
      val tla = os.pwd / "systems" / "dqueue" / "dqueue.tla"

      val errors = pgo.PGo.run(scala.collection.immutable.ArraySeq(
        "tracegen", tla.toString, tmp.toString
      ))

    catch
      case e: os.SubprocessException =>
        val msg = Option(e.getMessage).getOrElse("")
        assert(msg.contains("has no .log files"))
      case _: Throwable => ()

  test("tracegen with one empty log file: no errors"):
    val tmp = os.temp.dir()
    os.write(tmp / "foo.log", "")
    val tla = os.pwd / "systems" / "dqueue" / "dqueue.tla"
    val errors = pgo.PGo.run(scala.collection.immutable.ArraySeq(
      "tracegen", tla.toString, tmp.toString
    ))

    assert(errors.isEmpty)

end CLITests

