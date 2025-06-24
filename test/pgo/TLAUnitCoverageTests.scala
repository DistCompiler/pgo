package pgo

import pgo.model.SourceLocation.UnderlyingFile
import pgo.parser.TLAParser

final class TLAUnitCoverageTests extends munit.FunSuite:
  def checkNames(tlaFile: os.Path, names: List[String])(using
      munit.Location,
  ): Unit =
    test(s"unit coverage ${tlaFile.relativeTo(os.pwd)}"):
      val fileContents = os.read(tlaFile)
      val underlyingFile = UnderlyingFile(tlaFile)
      val module = TLAParser.readModule(underlyingFile, fileContents)

      val actualNames = module.units.view
        .flatMap(_.definitions)
        .flatMap(_.singleDefinitions)
        .map(_.canonicalIdString)
        .toList

      assertEquals(actualNames, names)
  end checkNames

  checkNames(
    tlaFile = os.pwd / "test" / "files" / "tla" / "simple.tla",
    names = List(
      "x",
      "y",
      "Inc",
      "UseTLC",
      "List",
      "Init",
    ),
  )
