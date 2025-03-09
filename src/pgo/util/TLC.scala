package pgo.util

object TLC:
  private lazy val theTools = os.temp(
    contents = os.read.stream(os.resource / "tla2tools.jar"),
    prefix = "tla2tools",
    suffix = ".jar",
  )
  private lazy val theCommunityModules = os.temp(
    contents = os.read.stream(os.resource / "CommunityModules-deps.jar"),
    prefix = "CommunityModules-deps.jar",
    suffix = ".jar",
  )

  def runToolbox(cwd: os.Path = os.pwd, javaOpts: List[os.Shellable] = Nil)(
      parts: os.Shellable*,
  ): Unit =
    val proc = os.proc(
      "java",
      "-XX:+UseParallelGC",
      javaOpts,
      "-classpath",
      s"$theTools:$theCommunityModules",
      parts,
    )

    println(s"$$ ${proc.commandChunks.mkString(" ")}")
    proc.call(cwd = cwd, stderr = os.Inherit, stdout = os.Inherit)

  def runTLC(cwd: os.Path = os.pwd, javaOpts: List[os.Shellable] = Nil)(
      parts: os.Shellable*,
  ): Unit =
    runToolbox(cwd, javaOpts)("tlc2.TLC", parts)

  def translatePCal(
      cwd: os.Path = os.pwd,
      specFile: os.Path,
      javaOpts: List[os.Shellable] = Nil,
  ): Unit =
    runToolbox(cwd, javaOpts)("pcal.trans", specFile)
