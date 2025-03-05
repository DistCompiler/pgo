val toolsDir = os.pwd / ".tools"
val toolsPath = toolsDir / "tla2tools.jar"
val communityModulesPath = toolsDir / "CommunityModules-deps.jar"

if os.exists(toolsDir)
then
  os.list(toolsDir)
    .filter(_.last.endsWith(".jar"))
    .foreach(os.remove)

locally:
  val result = requests.get("https://nightly.tlapl.us/dist/tla2tools.jar")
  os.write(toolsPath, result, createFolders = true)
  println(s"added/replaced $toolsPath")

locally:
  val result = requests.get(
    "https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules-deps.jar",
  )
  os.write(communityModulesPath, result, createFolders = true)
  println(s"added/replaced $communityModulesPath")
