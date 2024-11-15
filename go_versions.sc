//val minGoVersion = "1.22"

os.walk(os.pwd)
  .filter(os.isDir)
  .filter(dir => os.exists(dir / "go.mod"))
  .foreach { dir =>
    println(s"updating $dir...")

    os.call(List("go", "get", "-u"), cwd = dir)
    os.call(List("go", "mod", "tidy"), cwd = dir)

    // val modLines = os.read.lines(dir / "go.mod")

    // os.write.over(dir / "go.mod", modLines
    //   .iterator
    //   .flatMap {
    //     case s"go $version" => Iterator.single(s"go $minGoVersion")
    //     case s"toolchain $_" => Iterator.empty
    //     case line => Iterator.single(line)
    //   }
    //   .map(_ ++ "\n")
    // )
  }
