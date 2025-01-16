val toolsVersion = "1.8.0"
val communityModulesVersion = "202409181925"
val toolsDir = os.pwd / ".tools"
val toolsPath = toolsDir / s"tla2tools-$toolsVersion.jar"
val communityModulesPath = toolsDir / s"CommunityModules-deps.jar"

if os.exists(toolsDir)
then
  os.list(toolsDir)
    .filter(_.last.startsWith("tla2tools-"))
    .filter(_ != toolsPath)
    .foreach(os.remove)

  os.list(toolsDir)
    .filter(_.last.startsWith("CommunityModules-"))
    .filter(_ != communityModulesPath)
    .foreach(os.remove)

if !os.exists(toolsPath)
then
  val result = requests.get(
    s"https://github.com/tlaplus/tlaplus/releases/download/v$toolsVersion/tla2tools.jar"
  )
  os.write(toolsPath, result.bytes, createFolders = true)

if !os.exists(communityModulesPath)
then
  val result = requests.get(
    "https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules-deps.jar"
  )
  os.write(communityModulesPath, result.bytes, createFolders = true)
