package pgo.parser

import java.nio.file.{Files, Path}

object ParserTestingUtils {
  def ensureBackingFile(str: String): Path = {
    val path = Files.createTempFile("backing-file", "")
    path.toFile.deleteOnExit()
    Files.writeString(path, str)
    path
  }
}
