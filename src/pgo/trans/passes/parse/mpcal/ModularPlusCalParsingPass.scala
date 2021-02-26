package pgo.trans.passes.parse.mpcal

import pgo.model.mpcal.ModularPlusCalBlock
import pgo.model.tla.TLAModule
import pgo.parser.ModularPlusCalParser

import java.nio.file.Path

object ModularPlusCalParsingPass {
  def hasModularPlusCalBlock(inputFileName: Path, inputFileContents: CharSequence) =
    ModularPlusCalParser.hasModularPlusCalBlock(inputFileName, inputFileContents)

  def perform(inputFileName: Path, inputFileContents: CharSequence, tlaModule: TLAModule): ModularPlusCalBlock =
    ModularPlusCalParser.readBlock(inputFileName, inputFileContents, tlaModule)
}