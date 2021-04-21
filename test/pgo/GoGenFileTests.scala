package pgo

class GoGenFileTests extends FileTestSuite {
  override val testFiles: List[os.Path] = (os.list.stream(os.pwd / "test" / "files" / "gogen") ++
    os.list.stream(os.pwd / "test" / "files" / "semantics"))
    .filter(_.last.endsWith(".tla"))
    .toList

  testFiles.foreach { testFile =>
    test(s"gogen ${testFile.relativeTo(os.pwd)}") {
      val outFile = os.temp()
      val errors = PGo.run(Seq("gogen", "-s", testFile.toString(), "-o", outFile.toString()))
      checkErrors(errors, testFile)
      if(errors.isEmpty) {
        // TODO: check Go compilation
      }
    }
  }
}
