#!/usr/bin/env -S scala-cli shebang
//> using dep com.lihaoyi::os-lib:0.11.3
//> using dep "com.lihaoyi::requests:0.9.0"

val toolsVersion = "1.7.4"
val toolsDir = os.pwd / ".tools"
val toolsPath = toolsDir / s"tla2tools-$toolsVersion.jar"

if os.exists(toolsDir)
then
  os.list(toolsDir)
    .filter(_.last.startsWith("tla2tools-"))
    .filter(_ != toolsPath)
    .foreach(os.remove)

if !os.exists(toolsPath)
then
  val result = requests.get(
    s"https://github.com/tlaplus/tlaplus/releases/download/v$toolsVersion/tla2tools.jar"
  )
  os.write(toolsPath, result.bytes, createFolders = true)
