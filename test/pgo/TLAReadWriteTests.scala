package pgo

import pgo.parser.TLAParser
import pgo.model.SourceLocation.UnderlyingFile
import pgo.trans.TLARenderPass
import pgo.model.SourceLocation.UnderlyingString
import munit.diff.DiffOptions
import pgo.model.tla.TLAModule
import munit.diff.Printer

final class TLAReadWriteTests extends munit.FunSuite:
  val allTLAFiles = os
    .walk(os.pwd)
    .filter(os.isFile)
    .filter(_.last.endsWith(".tla"))
    // generated Validate files use IOUtils, which we don't support (yet)
    // TODO: properly scope all operators from TLC, std, community modules, by reading the corresponding TLA+
    .filterNot(_.last.endsWith("Validate.tla"))

  allTLAFiles.foreach: tlaFile =>
    val fileContents = os.read(tlaFile)
    if !fileContents.contains(":: expectedError")
    then
      test(s"TLA+ read/write ${tlaFile.relativeTo(os.pwd)}"):
        val underlyingFile = UnderlyingFile(tlaFile)
        val module = TLAParser.readModule(underlyingFile, fileContents)

        val reprintedFile = TLARenderPass
          .describeUnit(module)
          .linesIterator
          .mkString("\n")
        val reprintedUnderlying = UnderlyingString(reprintedFile, "<reprinted>")
        clue(reprintedFile)

        val reparsedModule =
          TLAParser.readModule(reprintedUnderlying, reprintedFile)

        given DiffOptions = DiffOptions.default.withPrinter:
          Some:
            Printer:
              case module: TLAModule =>
                TLARenderPass
                  .describeUnit(module)
                  .linesIterator
                  .mkString("\n")

        assertEquals(reparsedModule, module)
end TLAReadWriteTests
