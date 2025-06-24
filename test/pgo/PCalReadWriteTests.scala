package pgo

import pgo.util.Description
import pgo.model.SourceLocation
import pgo.parser.{PCalParser, TLAParser}
import Description._
import pgo.trans.PCalRenderPass

class PCalReadWriteTests extends munit.FunSuite {
  def check(path: os.Path)(using loc: munit.Location): Unit = {
    test(s"pcal read/write ${path.relativeTo(projectRoot).toString()}") {
      val underlying = new SourceLocation.UnderlyingFile(path)
      val fileContents = os.read(path)
      clue(s"original file:\n$fileContents")
      val tlaModule = TLAParser.readModuleBeforeTranslation(
        underlying = underlying,
        seq = fileContents,
      )
      val pcalAlgorithm = PCalParser.readAlgorithm(
        underlying = underlying,
        contents = fileContents,
        tlaModule = tlaModule,
      )

      val renderedContentsLines =
        d"(*\n${PCalRenderPass(pcalAlgorithm)}\n*)".linesIterator.toBuffer
      val renderedContents = renderedContentsLines.mkString("\n")

      clue(d"rendered file:\n$renderedContents")

      val reparsedAlgorithm = PCalParser.readAlgorithm(
        new SourceLocation.UnderlyingString(renderedContents),
        renderedContents,
        tlaModule,
      )

      assertEquals(reparsedAlgorithm, pcalAlgorithm)
    }
  }

  locally {
    val tlaDir = projectRoot / "test" / "files" / "tla"
    check(tlaDir / "Queens.tla")
    check(tlaDir / "Euclid.tla")
    check(tlaDir / "pgo2pc.tla")
    check(tlaDir / "2pc.tla")
    check(tlaDir / "round_robin.tla")
    check(tlaDir / "counter.tla")
    check(tlaDir / "DijkstraMutex.tla")
  }

  def checkWholeFolder(folder: os.Path): Unit = {
    os.list
      .stream(folder)
      .filter(_.last.endsWith(".tla.expectpcal"))
      .foreach(check)
  }

  checkWholeFolder(projectRoot / "test" / "files" / "general")
  checkWholeFolder(projectRoot / "test" / "files" / "pcalgen")
}
