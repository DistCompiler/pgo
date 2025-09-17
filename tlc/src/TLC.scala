package pgo.util

object TLC:
  lazy val theTLCModules = os.temp(
    contents = os.read.stream(os.resource / "TLCModules.zip"),
    prefix = "TLCModules",
    suffix = ".zip",
  )
  lazy val theStandardModules = os.temp(
    contents = os.read.stream(os.resource / "StandardModules.zip"),
    prefix = "StandardModules",
    suffix = ".zip",
  )
  lazy val theCommunityModules = os.temp(
    contents = os.read.stream(os.resource / "CommunityModules.zip"),
    prefix = "CommunityModules",
    suffix = ".zip",
  )

  def runToolbox(
      cwd: os.Path = os.pwd,
      javaOpts: List[os.Shellable] = Nil,
      outFile: Option[os.Path] = None,
  )(
      parts: os.Shellable*,
  ): Unit =
    val javaHome = os.Path(System.getProperty("java.home"))
    val proc = os.proc(
      javaHome / "bin" / "java",
      "-XX:+UseParallelGC",
      javaOpts,
      "-classpath",
      System.getProperty("java.class.path"),
      parts,
    )

    val subdir =
      if cwd.startsWith(os.pwd)
      then cwd.subRelativeTo(os.pwd)
      else cwd

    println(
      s"[$subdir]$$ ${proc.commandChunks.mkString(" ")}",
    )
    outFile match
      case None =>
        proc.call(cwd = cwd, stderr = os.Inherit, stdout = os.Inherit)
      case Some(outFile) =>
        proc.call(
          cwd = cwd,
          stdout = os.PathRedirect(outFile),
          mergeErrIntoOut = true,
        )

  def runTLC(
      cwd: os.Path = os.pwd,
      javaOpts: List[os.Shellable] = Nil,
      outFile: Option[os.Path] = None,
  )(
      parts: os.Shellable*,
  ): Unit =
    runToolbox(cwd, javaOpts, outFile)("tlc2.TLC", parts)

  def translatePCal(
      cwd: os.Path = os.pwd,
      specFile: os.Path,
      javaOpts: List[os.Shellable] = Nil,
  ): Unit =
    runToolbox(cwd, javaOpts)("pcal.trans", specFile)
