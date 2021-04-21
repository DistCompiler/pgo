package pgo

class PCalGenFileTests extends FileTestSuite {
  override val testFiles: List[os.Path] = (os.list.stream(os.pwd / "test" / "files" / "pcalgen") ++
    os.list.stream(os.pwd / "test" / "files" / "semantics"))
    .filter(_.last.endsWith(".tla"))
    .toList

  testFiles.foreach { testFile =>
    test(s"pcalgen ${testFile.relativeTo(os.pwd)}") {
      val tmpFile = os.temp(contents = testFile.toSource)
      val errors = PGo.run(Seq("pcalgen", "-s", tmpFile.toString()))
      checkErrors(errors, testFile)
      if(errors.isEmpty) {
        // TODO: check PCal compilation
      }
    }
  }
}