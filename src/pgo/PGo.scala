package pgo

import org.rogach.scallop
import org.rogach.scallop.{ScallopConf, ScallopOption, Subcommand, ValueConverter}
import os.Path
import pgo.model.{PGoError, SourceLocation}
import pgo.model.mpcal.MPCalBlock
import pgo.model.pcal.PCalAlgorithm
import pgo.model.tla.TLAModule
import pgo.parser.{MPCalParser, PCalParser, ParseFailureError, ParsingUtils, TLAParser}
import pgo.trans.{MPCalGoCodegenPass, MPCalNormalizePass, MPCalPCalCodegenPass, MPCalSemanticCheckPass, PCalRenderPass}
import pgo.util.Description
import pgo.util.Description._

import java.io.RandomAccessFile
import java.nio.channels.FileChannel
import java.nio.charset.StandardCharsets
import scala.util.Using
import scala.util.parsing.combinator.RegexParsers

object PGo {
  implicit val pathConverter: ValueConverter[Path] = scallop.singleArgConverter(os.Path(_, os.pwd))

  class Config(arguments: Seq[String]) extends ScallopConf(arguments) {
    banner("PGo compiler")
    trait Cmd { self: ScallopConf =>
      val specFile: ScallopOption[Path] = opt[os.Path](required = true)
      addValidation {
        if(os.exists(specFile())) {
          Right(())
        } else {
          Left(s"spec file ${specFile()} does not exist")
        }
      }
    }
    object GoGenCmd extends Subcommand("gogen") with Cmd {
      val outFile: ScallopOption[Path] = opt[os.Path](required = true)
      val packageName: ScallopOption[String] = opt[String](required = false)
    }
    addSubcommand(GoGenCmd)
    object PCalGenCmd extends Subcommand("pcalgen") with Cmd {
      // pass
    }
    addSubcommand(PCalGenCmd)

    // one of the subcommands must be passed
    addValidation {
      subcommand match {
        case Some(_) => Right(())
        case None => Left(s"a subcommand must be given")
      }
    }

    errorMessageHandler = { errMsg =>
      errMsg.linesIterator.foreach { line =>
        println(s"$printedName: $line")
      }
      printHelp()
      sys.exit(1)
    }

    verify()
  }

  private def charBufferFromFile(file: os.Path, use: Using.Manager): java.nio.CharBuffer = {
    val fileChannel = use(new RandomAccessFile(file.toIO, "r").getChannel)
    val buffer = fileChannel.map(FileChannel.MapMode.READ_ONLY, 0, fileChannel.size)
    StandardCharsets.UTF_8.decode(buffer)
  }

  private def parseMPCal(specFile: os.Path): (TLAModule, MPCalBlock) = {
    val underlyingFile = new SourceLocation.UnderlyingFile(specFile)
    Using.Manager { use =>
      val charBuffer = charBufferFromFile(specFile, use = use)

      val tlaModule = TLAParser.readModuleBeforeTranslation(underlyingFile, charBuffer)
      val mpcalBlock = MPCalParser.readBlock(underlyingFile, charBuffer, tlaModule)
      (tlaModule, mpcalBlock)
    }.get
  }

  private def parsePCal(specFile: os.Path): (TLAModule, PCalAlgorithm) = {
    val underlyingFile = new SourceLocation.UnderlyingFile(specFile)
    Using.Manager { use =>
      val charBuffer = charBufferFromFile(specFile, use = use)

      val tlaModule = TLAParser.readModuleBeforeTranslation(underlyingFile, charBuffer)
      val pcalAlgorithm = PCalParser.readAlgorithm(underlyingFile, charBuffer, tlaModule)
      (tlaModule, pcalAlgorithm)
    }.get
  }

  sealed abstract class PCalWriteError extends PGoError with PGoError.Error {
    override val errors: List[PGoError.Error] = List(this)
  }
  object PCalWriteError {
    final case class PCalTagsError(err: ParseFailureError) extends PCalWriteError {
      initCause(err)

      override val sourceLocation: SourceLocation = err.sourceLocation
      override val description: Description =
        d"one or both of `\\* BEGIN PLUSCAL TRANSLATION` and `\\* END PLUSCAL TRANSLATION` not found, or not found in the correct order;\n" +
          d"add these tags so that PGo knows where to put its generated PlusCal:\n" +
          err.description.indented
    }
  }

  def run(args: Seq[String]): List[PGoError.Error] = {
    val config = new Config(args)
    try {
      config.subcommand.get match {
        case config.GoGenCmd =>
          var (tlaModule, mpcalBlock) = parseMPCal(config.GoGenCmd.specFile())
          MPCalSemanticCheckPass(tlaModule, mpcalBlock)
          mpcalBlock = MPCalNormalizePass(tlaModule, mpcalBlock)

          val goCode = MPCalGoCodegenPass(tlaModule, mpcalBlock, packageName = config.GoGenCmd.packageName.toOption)
          os.write.over(config.GoGenCmd.outFile(), goCode.linesIterator.map(line => s"$line\n"))

          val fmtResult = os.proc("go", "fmt", config.GoGenCmd.outFile()).call(cwd = os.pwd, check = false)
          if(fmtResult.exitCode != 0) {
            println("could not run go fmt on output. this probably isn't fatal, but the Go output might look a little odd")
          }

        case config.PCalGenCmd =>
          var (tlaModule, mpcalBlock) = parseMPCal(config.PCalGenCmd.specFile())
          MPCalSemanticCheckPass(tlaModule, mpcalBlock)
          mpcalBlock = MPCalNormalizePass(tlaModule, mpcalBlock)

          val pcalAlgorithm = MPCalPCalCodegenPass(tlaModule, mpcalBlock)
          val renderedPCal = PCalRenderPass(pcalAlgorithm)

          val tempOutput = os.temp(dir = os.pwd)
          locally {
            /**
             * A simple parser that splits ("chops") an MPCal-containing TLA+ file into 3 parts:
             * - the bit before the PlusCal translation area
             * - the PlusCal translation area (which is not returned)
             * - the bit after the PlusCal translation area
             *
             * the before- and after- parts can be combined with a new PlusCal translation in order to insert a new
             *  translation
             */
            object PCalChopParser extends RegexParsers with ParsingUtils {
              override val skipWhitespace: Boolean = false // as usual, let us handle all the spacing explicitly

              val ws: Parser[String] = raw"""(?!\n)\s+""".r
              val pcalBeginTranslation: Parser[Unit] =
                ((ws.? ~> "\\*" ~> ws ~> "BEGIN" ~> ws ~> "PLUSCAL" ~> ws ~> "TRANSLATION" ~> ws.? ~> "\n") ^^^ ())
                  .withFailureMessage("`\\* BEGIN PLUSCAL TRANSLATION`, modulo whitespace, expected")
              val pcalEndTranslation: Parser[Unit] =
                ((ws.? ~> "\\*" ~> ws ~> "END" ~> ws ~> "PLUSCAL" ~> ws ~> "TRANSLATION" ~> ws.? ~> "\n") ^^^ ())
                  .withFailureMessage("`\\* END PLUSCAL TRANSLATION`, modulo whitespace, expected")
              val anyLine: Parser[String] = (rep(acceptIf(_ != '\n')(ch => s"'$ch' was a newline'")) <~ "\n").map(_.mkString)

              val nonMarkerLine: Parser[String] = not(pcalBeginTranslation | pcalEndTranslation) ~> anyLine

              val theChop: Parser[(List[String],List[String])] =
                phrase {
                  rep(nonMarkerLine) ~
                    (pcalBeginTranslation ~> rep(nonMarkerLine) ~> pcalEndTranslation ~> (rep(nonMarkerLine) ~
                      (not(pcalBeginTranslation | pcalEndTranslation) ~> rep1(acceptIf(_ != '\n')(ch => s"'$ch' was a newline")).map(_.mkString).?)))
                } ^^ {
                  case linesBefore ~ (linesAfter ~ lastLine) =>
                    // note: lastLine accounts for cases where a file is not \n-terminated... which happens somewhat often, and
                    //       confuses the line detection method used in anyLine, which relies on all lines having a trailing \n
                    (linesBefore, linesAfter ++ lastLine)
                }

              def parseTheChop(file: os.Path): (List[String],List[String]) = {
                val underlyingText = new SourceLocation.UnderlyingFile(file)
                Using.Manager { use =>
                  val reader = buildReader(charBufferFromFile(file, use), underlyingText)
                  checkResult(theChop(reader))
                }.get
              }
            }

            val renderedPCalIterator = Iterator("\\* BEGIN PLUSCAL TRANSLATION") ++
              renderedPCal.linesIterator ++
              Iterator("", "\\* END PLUSCAL TRANSLATION")

            try {
              os.write.over(tempOutput, PCalChopParser.parseTheChop(config.PCalGenCmd.specFile()) match {
                case (beforeLines, afterLines) =>
                  (beforeLines.iterator ++ renderedPCalIterator ++ afterLines.iterator)
                    .flatMap(line => Iterator(line, "\n"))
              })
            } catch {
              case err: ParseFailureError => throw PCalWriteError.PCalTagsError(err) // wrap error for UI; this is a special parse error
            }
          }

          // move the rendered output over the spec file, replacing it
          os.move(from = tempOutput, to = config.PCalGenCmd.specFile(), replaceExisting = true, atomicMove = true)

          // run a free-standing semantic check on the generated code, in case our codegen doesn't agree with our
          // own semantic checks (which would be a bug!)
          locally {
            try {
              val (tlaModule, pcalAlgorithm) = parsePCal(config.PCalGenCmd.specFile())
              MPCalSemanticCheckPass(tlaModule, MPCalBlock.fromPCalAlgorithm(pcalAlgorithm))
            } catch {
              case err: PGoError =>
                throw MPCalSemanticCheckPass.SemanticError(
                  err.errors.map(MPCalSemanticCheckPass.SemanticError.ConsistencyCheckFailed))
            }
          }
      }
      Nil
    } catch {
      case err: PGoError =>
        err.errors
          // ensure you don't see the same msg twice
          .distinctBy(e => (e.sourceLocation.longDescription + d"\n" + e.description).linesIterator.mkString("\n"))
    }
  }

  def main(args: Array[String]): Unit = {
    val errors = run(args)
    if(errors.nonEmpty) {
      d"failed:${
        errors.view.map(err => d"\n${err.description} at ${err.sourceLocation.longDescription.indented}")
          .flattenDescriptions
      }"
        .linesIterator
        .foreach(System.err.println)
      sys.exit(1)
    }
  }
}
