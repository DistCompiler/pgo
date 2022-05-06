package pgo

import org.scalatest.tagobjects.Slow

class TLCTests extends FileTestSuite {
  private val systemFiles = os.list.stream(os.pwd / "systems")
    .map(folder => os.list.stream(folder))
    .flatMap(_.find(_.last.endsWith(".tla")))
    .toList

  override val testFiles: List[os.Path] =  systemFiles

  private val javaBin =  os.Path(System.getProperty("java.home"), os.pwd) / "bin" / "java"
  private val tla2Tools = os.pwd / "tools" / "tla2tools.jar"

  def runTLAMake(testFile: os.Path, args: os.Shellable*): Unit = {
    os.proc("make", s"JAVA=$javaBin", s"TLA2TOOLS_JAR=$tla2Tools", args)
      .call(cwd = testFile / os.up)
  }

  def setupForTLC(testFile: os.Path): Unit = {
    val goTestsDir = testFile / os.up
    val outFile = goTestsDir / s"${testFile.last}.outpcal"

    os.copy.over(from = testFile, to = outFile)

    val errors = PGo.run(Seq("pcalgen", "-s", outFile.toString()))
    checkErrors(errors, testFile)
    assert(errors.isEmpty)
    os.move.over(from = outFile, to = testFile)

    runTLAMake(testFile, "tlaplusgen")
    runTLAMake(testFile, "sany")
  }

  testFiles.foreach { testFile =>
    test(s"tlc sim ${testFile.relativeTo(os.pwd)}", Slow) {
      setupForTLC(testFile)
      runTLAMake(testFile, "sim")
    }

//    test(s"tlc mc ${testFile.relativeTo(os.pwd)}", Slow) {
//      setupForTLC(testFile)
//      runTLAMake(testFile, "mc")
//    }
  }
}
