package pgo

class GoGenFileTests extends FileTestSuite {
  private val plainTestFiles = (os.list.stream(os.pwd / "test" / "files" / "general") ++
    os.list.stream(os.pwd / "test" / "files" / "gogen"))
    .filter(_.last.endsWith(".tla"))
    .toList

  private val systemFiles = os.list.stream(os.pwd / "systems")
    .map(folder => os.list.stream(folder))
    .flatMap(_.find(_.last.endsWith(".tla")))
    .toList

  override val testFiles: List[os.Path] = plainTestFiles ++ systemFiles

  testFiles.foreach { testFile =>
    test(s"gogen ${testFile.relativeTo(os.pwd)}") {
      val outDir = os.temp.dir()
      val goTestsDir =
        if(testFile.relativeTo(os.pwd).startsWith(os.rel / "systems")) {
          testFile / os.up
        } else {
          testFile / os.up / s"${testFile.last}.gotests"
        }

      if(os.isDir(goTestsDir)) { // should only do something useful when PGo isn't expected to error out
        os.copy.over(from = goTestsDir, to = outDir, createFolders = true)
        // rewrite go.mod to point to the absolute path of our local copy of the distsys library
        val distsysReplaceRgx = raw"""replace github.com/UBC-NSS/pgo/distsys => .*""".r
        os.write.over(outDir / "go.mod", os.read.lines(outDir / "go.mod").view.flatMap {
          case distsysReplaceRgx() => Some(s"replace github.com/UBC-NSS/pgo/distsys => ${os.pwd / "distsys"}")
          case line => Some(line)
        }.map(line => s"$line\n"))
      }

      val outFile = outDir / s"${testFile.baseName}.go"

      // use a tag file to conditionally re-enable multiple writes checking
      val noMultipleWrites = if(getNoMultipleWrites(testFile)) {
        Seq("--no-multiple-writes")
      } else {
        Seq.empty
      }
      val errors = PGo.run(noMultipleWrites ++ Seq("gogen", "-s", testFile.toString(), "-o", outFile.toString()))
      checkErrors(errors, testFile)
      if(errors.isEmpty) {
        assert(os.exists(goTestsDir)) // sanity
        if(!sys.env.contains("TESTS_DO_NOT_WRITE")) {
          // unless the environment var above is set, write the output file into the test files, so the test can
          // be debugged / manipulated using standard Go tools
          os.write.over(goTestsDir / outFile.last, outFile.toSource)
          // auto-tidy the copied files, so we can keep the setups up to date
          os.proc(goExe, "mod", "tidy").call(cwd = goTestsDir)
        }
        // try to run tests in Go, subprocess failure will count as a test failure
        // see above for where to find generated code to debug
        os.proc(goExe, "build").call(cwd = outDir)
        os.proc(goExe, "test", "-v").call(cwd = outDir)
        os.proc(goExe, "test", "-race", "-v").call(cwd = outDir)
      }
    }
  }
}
