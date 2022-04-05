package pgo

import ammonite.interp.api.AmmoniteExit
import ammonite.util.Res
import org.rogach.scallop
import org.rogach.scallop.{LazyMap, ScallopConf, ScallopOption, Subcommand, ValueConverter}
import pgo.checker.{StateExplorer, TraceChecker, TraceElement}
import pgo.model.{PGoError, RefersTo, SourceLocation, Visitable}
import pgo.model.mpcal.MPCalBlock
import pgo.model.pcal.PCalAlgorithm
import pgo.model.tla.{TLAConstantDeclaration, TLAModule, TLAOpDecl}
import pgo.parser.{MPCalParser, PCalParser, ParseFailureError, ParsingUtils, TLAParser}
import pgo.trans.{MPCalGoCodegenPass, MPCalNormalizePass, MPCalPCalCodegenPass, MPCalSemanticCheckPass, PCalRenderPass}
import pgo.util.{!!!, ById, Description}
import pgo.util.Description._
import pgo.util.TLAExprInterpreter.TLAValue

import java.io.RandomAccessFile
import java.nio.channels.FileChannel
import java.nio.charset.StandardCharsets
import scala.collection.immutable.ArraySeq
import scala.collection.mutable
import scala.concurrent.duration.{Duration, MILLISECONDS}
import scala.util.Using
import scala.util.parsing.combinator.RegexParsers

object PGo {
  implicit val pathConverter: ValueConverter[os.Path] = scallop.singleArgConverter(os.Path(_, os.pwd))
  implicit val tlaValueConverter: ValueConverter[TLAValue] = scallop.singleArgConverter(TLAValue.parseFromString)
  implicit val tlaValuePropsConverter: ValueConverter[Map[String,TLAValue]] = scallop.propsConverter(tlaValueConverter)

  class Config(arguments: Seq[String]) extends ScallopConf(arguments) {
    banner("PGo compiler")

    val noMultipleWrites: ScallopOption[Boolean] = opt[Boolean](required = true, default = Some(false),
      descr = "whether to allow multiple assignments to the same variable within the same critical section. PCal does not. defaults to false.")

    trait Cmd { self: ScallopConf =>
      val specFile: ScallopOption[os.Path] = opt[os.Path](required = true, descr = "the .tla specification to operate on.")
      addValidation {
        if(os.exists(specFile())) {
          Right(())
        } else {
          Left(s"spec file ${specFile()} does not exist")
        }
      }
    }
    object GoGenCmd extends Subcommand("gogen") with Cmd {
      val outFile: ScallopOption[os.Path] = opt[os.Path](required = true, descr = "the output .go file to write to.")
      val packageName: ScallopOption[String] = opt[String](required = false, descr = "the package name within the generated .go file. defaults to a normalization of the MPCal block name.")
    }
    addSubcommand(GoGenCmd)
    object PCalGenCmd extends Subcommand("pcalgen") with Cmd {
      // pass
    }
    addSubcommand(PCalGenCmd)
    object TraceCheckCmd extends Subcommand("tracecheck") with Cmd {
      val configFile: ScallopOption[os.Path] = opt[os.Path](required = false, descr = "additional options specified in Scala, use for structured options")
      val traceFile: ScallopOption[os.Path] = opt[os.Path](required = false, descr = "the structured log file to check.")
      val constants: LazyMap[String, TLAValue] = props[TLAValue](
        name = 'C',
        descr = "the constants value bindings to assume while checking.",
        keyName = "name",
        valueName = "TLA+ value")

      addValidation {
        traceFile.toOption match {
          case Some(_) => Right(())
          case None => Left(s"a trace file must be provided")
        }
      }
    }
    addSubcommand(TraceCheckCmd)

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

  final case class PGoAmmoniteConfigMissingError() extends PGoError with PGoError.Error {
    val errors: List[PGoError.Error] = List(this)
    def description: Description = d"the provided config file did not produce config when executed"
    def sourceLocation: SourceLocation = SourceLocation.unknown
  }

  final case class PGoAmmoniteError(failing: Res.Failing) extends PGoError with PGoError.Error {
    val errors: List[PGoError.Error] = List(this)
    def description: Description = d"error executing config file: ${
      failing match {
        case Res.Failure(msg) => msg
        case Res.Exception(t, msg) => d"$msg: ${
          val stringWriter = new java.io.StringWriter()
          val printWriter = new java.io.PrintWriter(stringWriter)
          t.printStackTrace(printWriter)
          stringWriter.toString
        }"
        case Res.Skip => !!!
        case Res.Exit(_) => !!!
      }}"
    def sourceLocation: SourceLocation = SourceLocation.unknown
  }

  final case class TraceCheckerUserConfig(constantDefinitions: Map[String, TLAValue] = Map.empty)
  object TraceCheckerUserConfig {
    final class Builder private[TraceCheckerUserConfig] (private[TraceCheckerUserConfig] var config: TraceCheckerUserConfig) {
      def constant(name: String)(value: TLAValue): Unit = {
        config = config.copy(constantDefinitions = config.constantDefinitions.updated(name, value))
      }
    }

    def build(fn: Builder => Unit): Nothing = {
      val builder = new Builder(TraceCheckerUserConfig())
      fn(builder)
      throw AmmoniteExit(builder.config)
    }
  }

  def charBufferFromFile(file: os.Path, use: Using.Manager): java.nio.CharBuffer = {
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

  final case class FileSystemError(err: java.nio.file.FileSystemException) extends PGoError with PGoError.Error {
    initCause(err)

    override val errors: List[PGoError.Error] = List(this)
    override val sourceLocation: SourceLocation = SourceLocation.unknown
    override val description: Description = {
      val reason: Description = Option(err.getReason).map(reason => d": $reason").getOrElse(d"")
      val files: List[String] = Nil ++ Option(err.getFile) ++ Option(err.getOtherFile)

      val involvingFiles: Description =
        if(files.isEmpty) {
          d""
        } else {
          d" involving ${files.view.map(_.toDescription).separateBy(d" and ")}"
        }
      d"I/O error$involvingFiles$reason"
    }
  }

  def run(args: Seq[String]): List[PGoError.Error] = {
    val config = new Config(args)
    try {
      config.subcommand.get match {
        case config.GoGenCmd =>
          var (tlaModule, mpcalBlock) = parseMPCal(config.GoGenCmd.specFile())
          MPCalSemanticCheckPass(tlaModule, mpcalBlock, noMultipleWrites = config.noMultipleWrites())
          mpcalBlock = MPCalNormalizePass(tlaModule, mpcalBlock)

          val goCode = MPCalGoCodegenPass(tlaModule, mpcalBlock, packageName = config.GoGenCmd.packageName.toOption)
          os.write.over(config.GoGenCmd.outFile(), goCode.linesIterator.map(line => s"$line\n"))

          val fmtResult = os.proc("go", "fmt", config.GoGenCmd.outFile()).call(cwd = os.pwd, check = false)
          if(fmtResult.exitCode != 0) {
            println("could not run go fmt on output. this probably isn't fatal, but the Go output might look a little odd")
          }

        case config.PCalGenCmd =>
          var (tlaModule, mpcalBlock) = parseMPCal(config.PCalGenCmd.specFile())
          MPCalSemanticCheckPass(tlaModule, mpcalBlock, noMultipleWrites = config.noMultipleWrites())
          mpcalBlock = MPCalNormalizePass(tlaModule, mpcalBlock)

          val pcalAlgorithm = MPCalPCalCodegenPass(tlaModule, mpcalBlock)
          val renderedPCal = PCalRenderPass(pcalAlgorithm)

          val tempOutput = os.temp(dir = config.PCalGenCmd.specFile() / os.up, deleteOnExit = true)
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

          // move the rendered output over the spec file, replacing it.
          os.move(from = tempOutput, to = config.PCalGenCmd.specFile(), replaceExisting = true, atomicMove = true)

          // run a free-standing semantic check on the generated code, in case our codegen doesn't agree with our
          // own semantic checks (which would be a bug!)
          locally {
            try {
              val (tlaModule, pcalAlgorithm) = parsePCal(config.PCalGenCmd.specFile())
              MPCalSemanticCheckPass(tlaModule, MPCalBlock.fromPCalAlgorithm(pcalAlgorithm), noMultipleWrites = true)
            } catch {
              case err: PGoError =>
                throw MPCalSemanticCheckPass.SemanticError(
                  err.errors.map(MPCalSemanticCheckPass.SemanticError.ConsistencyCheckFailed))
            }
          }
        case config.TraceCheckCmd =>
          var (tlaModule, mpcalBlock) = parseMPCal(config.TraceCheckCmd.specFile())
          MPCalSemanticCheckPass(tlaModule, mpcalBlock, noMultipleWrites = config.noMultipleWrites())
          mpcalBlock = MPCalNormalizePass(tlaModule, mpcalBlock)

          val userConfig = config.TraceCheckCmd.configFile.toOption
            .map { configFile =>
              ammonite.Main().runScript(configFile, Seq.empty) match {
                case (Res.Success(_), _) => throw PGoAmmoniteConfigMissingError()
                case (Res.Exit(config), _) => config.asInstanceOf[TraceCheckerUserConfig]
                case (failing: Res.Failing, _) => throw PGoAmmoniteError(failing)
              }
            }
            .getOrElse(TraceCheckerUserConfig())

          // associate passed-in constants with definitions in the provided module(s)
          val constantsConfig = config.TraceCheckCmd.constants ++ userConfig.constantDefinitions
          val constantBindsRemaining =
            (constantsConfig.keysIterator ++ userConfig.constantDefinitions.keysIterator)
              .to(mutable.HashSet)
          val constantBinds = mutable.HashMap.empty[ById[RefersTo.HasReferences], TLAValue]
          val constantsExtractor: PartialFunction[Visitable,Unit] = {
            case TLAConstantDeclaration(decls) =>
              decls.foreach { decl =>
                decl.variant match {
                  case TLAOpDecl.NamedVariant(ident, _) =>
                    constantsConfig.get(ident.id).foreach { binding =>
                      constantBindsRemaining -= ident.id
                      constantBinds(ById(decl)) = binding
                    }
                  case TLAOpDecl.SymbolVariant(sym) =>
                    constantsConfig.get(sym.symbol.stringReprDefn).foreach { binding =>
                      constantBindsRemaining -= sym.symbol.stringReprDefn
                      constantBinds(ById(decl)) = binding
                    }
                }
              }
          }
          tlaModule.visit(Visitable.TopDownFirstStrategy)(constantsExtractor)
          mpcalBlock.visit(Visitable.TopDownFirstStrategy)(constantsExtractor)

          val traceChecker = new TraceChecker(stateExplorer = new StateExplorer(
            mpcalBlock = mpcalBlock,
            constants = constantBinds.toMap))

          os.read.lines.stream(config.TraceCheckCmd.traceFile())
            .map(upickle.default.read[ujson.Value](_))
            .map(TraceElement.fromJSON)
            .foreach(traceChecker.consumeTraceElement)

          val issueOpt = traceChecker.checkSpeculativePath().nextOption()
          issueOpt match {
            case None =>
              println("trace OK: no issues detected")
            case Some(issue) =>
              throw issue
          }
      }
      Nil
    } catch {
      case err: java.nio.file.FileSystemException =>
        List(FileSystemError(err))
      case err: PGoError =>
        err.errors
          // ensure you don't see the same msg twice
          .distinctBy(e => (e.sourceLocation.longDescription + d"\n" + e.description).linesIterator.mkString("\n"))
    }
  }

  def main(args: Array[String]): Unit = {
    val startTime = System.currentTimeMillis()
    val errors = run(ArraySeq.unsafeWrapArray(args))
    val endTime = System.currentTimeMillis()
    val duration = Duration(length = endTime - startTime, unit = MILLISECONDS)
    if(errors.nonEmpty) {
      d"failed in ${duration.toString()}:${
        errors.view.map(err => d"\n${err.description} at ${err.sourceLocation.longDescription.indented}")
          .flattenDescriptions
      }"
        .linesIterator
        .foreach(System.err.println)
      sys.exit(1)
    } else {
      System.err.println(s"ok in ${duration.toString()}")
    }
  }
}
