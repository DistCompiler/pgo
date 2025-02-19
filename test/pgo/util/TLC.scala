package pgo.util

object TLC:
  def runToolbox(cwd: os.Path)(parts: os.Shellable*): Unit =
    val theTools = os
      .list(os.pwd / ".tools")
      .find(_.lastOpt.exists(_.startsWith("tla2tools")))
      .get
    val theCommunityModules = os
      .list(os.pwd / ".tools")
      .find(_.lastOpt.exists(_.startsWith("CommunityModules-")))
      .get

    val proc = os.proc(
      "java",
      "-XX:+UseParallelGC",
      "-classpath",
      s"$theTools:$theCommunityModules",
      parts
    )

    println(s"$$ ${proc.commandChunks.mkString(" ")}")
    proc.call(cwd = cwd, mergeErrIntoOut = true, stdout = os.Inherit)

  def runTLC(cwd: os.Path)(parts: os.Shellable*): Unit =
    runToolbox(cwd)("tlc2.TLC", parts)

  def translatePCal(cwd: os.Path, specFile: os.Path): Unit =
    runToolbox(cwd)("pcal.trans", specFile)
