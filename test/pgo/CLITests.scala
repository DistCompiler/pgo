package pgo

class CLITests extends munit.FunSuite:
  private val cli =
    Seq[os.Shellable]("scala-cli", "run", ".", "--main-class", "pgo.PGo", "--")

  test("tracegen with no log files in dir"):
    val tmp = os.temp.dir() // some empty dir

    val result = os
      .proc(
        cli,
        "tracegen",
        os.pwd / "systems" / "dqueue" / "dqueue.tla",
        tmp,
      )
      .call(cwd = os.pwd, check = false)

    assertNotEquals(result.exitCode, 0)
    assert(result.toString().contains("has no .log files"))

  test("tracegen with one empty log file"):
    val tmp = os.temp.dir()
    os.write(tmp / "foo.log", "")

    os.proc(
      cli,
      "tracegen",
      os.pwd / "systems" / "dqueue" / "dqueue.tla",
      tmp,
    ).call(cwd = os.pwd)

    // TLC must not choke on the generated output,
    // despite there being 0 critical sections
    os.proc(cli, "tlc", tmp / "dqueueValidate.tla")
      .call()
end CLITests
