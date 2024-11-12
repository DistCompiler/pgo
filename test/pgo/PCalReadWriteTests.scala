package pgo

import org.scalactic.source.Position
import org.scalatest.funsuite.AnyFunSuite
import pgo.util.Description
import pgo.model.SourceLocation
import pgo.parser.{PCalParser, TLAParser}
import Description._
import pgo.trans.PCalRenderPass

class PCalReadWriteTests extends AnyFunSuite {
  def check(path: os.Path)(implicit pos: Position): Unit = {
    test(path.relativeTo(os.pwd).toString()) {
      val underlying = new SourceLocation.UnderlyingFile(path)
      val fileContents = os.read(path)
      withClue(s"original file:\n$fileContents") {
        val tlaModule = TLAParser.readModuleBeforeTranslation(
          underlying = underlying,
          seq = fileContents
        )
        val pcalAlgorithm = PCalParser.readAlgorithm(
          underlying = underlying,
          contents = fileContents,
          tlaModule = tlaModule
        )

        val renderedContentsLines =
          d"(*\n${PCalRenderPass(pcalAlgorithm)}\n*)".linesIterator.toBuffer
        val renderedContents = renderedContentsLines.mkString("\n")

        withClue(d"rendered file:\n$renderedContents") {
          val reparsedAlgorithm = PCalParser.readAlgorithm(
            new SourceLocation.UnderlyingString(renderedContents),
            renderedContents,
            tlaModule
          )

          assert(pcalAlgorithm == reparsedAlgorithm)
        }
      }
    }
  }

  locally {
    val tlaDir = os.pwd / "test" / "files" / "tla"
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

  checkWholeFolder(os.pwd / "test" / "files" / "general")
  checkWholeFolder(os.pwd / "test" / "files" / "pcalgen")
}
