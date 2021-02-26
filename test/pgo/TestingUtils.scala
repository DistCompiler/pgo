package pgo

import com.github.difflib.{DiffUtils, UnifiedDiffUtils}
import pgo.model.mpcal.ModularPlusCalBlock
import pgo.model.tla.TLAModule
import pgo.parser.{ModularPlusCalParser, TLAParser}

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters._

object TestingUtils {

  def stringDiff(expected: String, actual: String): List[String] = {
    val expectedLines = expected.linesIterator.toBuffer
    val actualLines = actual.linesIterator.toBuffer
    val patch = DiffUtils.diff(expectedLines.asJava, actualLines.asJava)

    UnifiedDiffUtils.generateUnifiedDiff("expected", "actual", expectedLines.asJava, patch, 3)
      .asScala.toList
  }

  def parseMPCalFromString(specStr: String): (Path,TLAModule,ModularPlusCalBlock) = {
    val temp = Files.createTempFile("mpcal-reparse", "")
    temp.toFile.deleteOnExit()
    Files.writeString(temp, specStr)
    val tlaModule = TLAParser.readModuleBeforeTranslation(temp, specStr)
    (temp, tlaModule, ModularPlusCalParser.readBlock(temp, specStr, tlaModule))
  }

  def reparseMPCal(mpcal: ModularPlusCalBlock): (Path,ModularPlusCalBlock) = {
    val mpcalStr =
      s"""
         |---- MODULE Before ----
         |EXTENDS Sequences, FiniteSets, Integers
         |(*
         |${mpcal.toString}
         |*)
         |${"\\"}* BEGIN TRANSLATION
         |====
         |""".stripMargin

    val temp = Files.createTempFile("mpcal-reparse", "")
    temp.toFile.deleteOnExit()
    Files.writeString(temp, mpcalStr)
    val tlaModule = TLAParser.readModuleBeforeTranslation(temp, mpcalStr)
    (temp, ModularPlusCalParser.readBlock(temp, mpcalStr, tlaModule))
  }
}
