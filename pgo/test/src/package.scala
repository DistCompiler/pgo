package pgo

lazy val projectRoot: os.Path =
  System.getenv("MILL_WORKSPACE_ROOT") match
    case null => os.pwd
    case path => os.Path(path)
end projectRoot
