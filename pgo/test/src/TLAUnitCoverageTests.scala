package pgo

import pgo.model.SourceLocation.UnderlyingFile
import pgo.parser.TLAParser
import pgo.model.DefinitionOne
import pgo.model.DefinitionComposite
import pgo.model.tla.TLAOperatorDefinition
import pgo.model.tla.TLANumber
import pgo.model.tla.TLANumber.DecimalSyntax
import pgo.model.tla.TLANumber.HexadecimalSyntax
import pgo.model.tla.TLANumber.BinarySyntax
import pgo.model.tla.TLANumber.OctalSyntax
import pgo.model.tla.TLANumber.IntValue

final class TLAUnitCoverageTests extends munit.FunSuite:
  def checkNames(tlaFile: os.Path, names: List[String])(using
      munit.Location,
  ): Unit =
    test(s"unit coverage ${tlaFile.relativeTo(projectRoot)}"):
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
    tlaFile = projectRoot / "pgo" / "test" / "files" / "tla" / "simple.tla",
    names = List(
      "x",
      "y",
      "Inc",
      "UseTLC",
      "List",
      "Init",
    ),
  )

  test("parsing numbers"):
    val tlaFile = projectRoot / "pgo" / "test" / "files" / "tla" / "Numbers.tla"
    val fileContents = os.read(tlaFile)
    val underlyingFile = UnderlyingFile(tlaFile)
    val module = TLAParser.readModule(underlyingFile, fileContents)

    val values = module.units.view
      .collect { case op: TLAOperatorDefinition =>
        op
      }
      .map { case TLAOperatorDefinition(name, args, body, isLocal) =>
        body
      }
      .collect { case num: TLANumber =>
        num
      }
      .toList

    val expected = List(
      TLANumber(IntValue(1), DecimalSyntax),
      TLANumber(IntValue(1), HexadecimalSyntax),
      TLANumber(IntValue(1), BinarySyntax),
      TLANumber(IntValue(1), OctalSyntax),
    )
    assertEquals(values, expected)
