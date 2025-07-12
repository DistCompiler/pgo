package pgo

import com.github.difflib.{DiffUtils, UnifiedDiffUtils}

import scala.jdk.CollectionConverters._
import scala.util.control.NonFatal

class PCalGenFileTests extends FileTestSuite {
  override val testFiles: List[os.Path] =
    (os.list.stream(projectRoot / "test" / "files" / "general") ++
      os.list.stream(projectRoot / "test" / "files" / "pcalgen"))
      .filter(_.last.endsWith(".tla"))
      .toList

  testFiles.foreach { testFile =>
    test(s"pcalgen ${testFile.relativeTo(projectRoot)}") {
      val tmpFile = os.temp(contents = testFile.toSource, suffix = ".tla")

      // use a tag file to conditionally re-enable multiple writes checking
      val noMultipleWrites = if (getNoMultipleWrites(testFile)) {
        Seq("--no-multiple-writes")
      } else {
        Seq.empty
      }
      val errors =
        PGo.run(noMultipleWrites ++ Seq("pcalgen", tmpFile.toString()))
      try {
        checkErrors(errors, testFile)
        if (errors.isEmpty) {
          val expectedFile = testFile / os.up / s"${testFile.last}.expectpcal"
          val expectedLines =
            if (os.exists(expectedFile)) os.read.lines(expectedFile)
            else IndexedSeq.empty
          val actualLines = os.read.lines(tmpFile)

          val patch = DiffUtils.diff(expectedLines.asJava, actualLines.asJava)
          val diff = UnifiedDiffUtils.generateUnifiedDiff(
            "expected",
            "actual",
            expectedLines.asJava,
            patch,
            5,
          )

          if (expectedLines != actualLines) {
            fail(s"expected PCal codegen did not match actual", clues(diff.asScala.mkString("\n")))
          }
        }
      } catch {
        case NonFatal(err) =>
          // during debugging, it helps to see the output file to which the errors were referring
          // if anything breaks past the end of the PGo run, this file will be there already and should be kept.
          if (!sys.env.contains("TESTS_DO_NOT_WRITE")) {
            os.write.over(
              testFile / os.up / s"${testFile.last}.outpcal",
              data = tmpFile.toSource,
            )
          }
          throw err
      }
    }
  }
}
