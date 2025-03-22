package pgo

import org.rogach.scallop
import org.rogach.scallop.{
  LazyMap,
  ScallopConf,
  ScallopOption,
  Subcommand,
  ValueConverter,
  given,
}
import pgo.model.{PGoError, RefersTo, SourceLocation, Visitable}
import pgo.model.mpcal.MPCalBlock
import pgo.model.pcal.PCalAlgorithm
import pgo.model.tla.{TLAConstantDeclaration, TLAModule, TLAOpDecl}
import pgo.parser.{
  MPCalParser,
  PCalParser,
  ParseFailureError,
  ParsingUtils,
  TLAParser,
}
import pgo.trans.{
  MPCalGoCodegenPass,
  MPCalNormalizePass,
  MPCalPCalCodegenPass,
  MPCalSemanticCheckPass,
  PCalRenderPass,
}
import pgo.util.{!!!, ById, Description}
import pgo.util.Description.{_, given}
import pgo.util.TLAExprInterpreter.TLAValue

import java.io.RandomAccessFile
import java.nio.channels.FileChannel
import java.nio.charset.StandardCharsets
import scala.collection.immutable.ArraySeq
import scala.collection.mutable
import scala.concurrent.duration.{Duration, MILLISECONDS}
import scala.util.Using
import scala.util.parsing.combinator.RegexParsers
import scala.concurrent.duration
import java.io.PrintStream
import java.io.PrintWriter
import java.io.StringWriter

object PGo {
  given pathConverter: ValueConverter[os.Path] =
    scallop.singleArgConverter(os.Path(_, os.pwd))
  given listOfPathConverter: ValueConverter[List[os.Path]] =
    scallop.listArgConverter(os.Path(_, os.pwd))
  given tlaValueConverter: ValueConverter[TLAValue] =
    scallop.singleArgConverter(TLAValue.parseFromString)
  given durationConverter: ValueConverter[duration.Duration] =
    scallop.singleArgConverter(duration.Duration.apply)
  given tlaValuePropsConverter: ValueConverter[Map[String, TLAValue]] =
    scallop.propsConverter(tlaValueConverter)
  given mpcalVariablesConverter
      : ValueConverter[Map[String, pgo.tracing.MPCalVariable]] =
    scallop.propsConverter:
      scallop.singleArgConverter:
        case s"local:$name"   => pgo.tracing.MPCalVariable.Local(name)
        case s"global:$name"  => pgo.tracing.MPCalVariable.Global(name)
        case s"mapping:$name" => pgo.tracing.MPCalVariable.Mapping(name)
        case str =>
          throw IllegalArgumentException(
            s"missing or incorrect prefix for $str",
          )

  class Config(arguments: Seq[String]) extends ScallopConf(arguments) {
    banner("PGo compiler")

    val noMultipleWrites: ScallopOption[Boolean] = opt[Boolean](
      required = true,
      default = Some(false),
      descr =
        "whether to allow multiple assignments to the same variable within the same critical section. PCal does not. defaults to false.",
    )

    trait Cmd { self: ScallopConf =>
      val specFile = trailArg[os.Path](
        required = true,
        descr = "the .tla specification to operate on.",
      )
      addValidation {
        if (os.exists(specFile())) {
          Right(())
        } else {
          Left(s"spec file ${specFile()} does not exist")
        }
      }
    }
    object GoGenCmd extends Subcommand("gogen") with Cmd {
      val outFile = opt[os.Path](
        required = true,
        descr = "the output .go file to write to.",
      )
      val packageName = opt[String](
        required = false,
        descr =
          "the package name within the generated .go file. defaults to a normalization of the MPCal block name.",
      )
    }
    addSubcommand(GoGenCmd)
    object PCalGenCmd extends Subcommand("pcalgen") with Cmd {
      // pass
    }
    addSubcommand(PCalGenCmd)
    object TraceGenCmd extends Subcommand("tracegen") {
      val specFile = trailArg[os.Path](descr =
        "the specification file from which to infer parameters",
      )
      val cfgFile = opt[os.Path](
        descr = "config file fragment to include in *Validate.cfg",
        default = Some(specFile() / os.up / s"${specFile().last.stripSuffix(".tla")}Validate${cfgFragmentSuffix()}.cfg"),
      )
      val destDir = trailArg[os.Path](
        required = true,
        descr = "directory into which code should be generated",
      )
      val logsDir = opt[os.Path](
        descr = "directory containing log files to use",
        default = Some(destDir()),
      )
      val cfgFragmentSuffix = opt[String](
        descr =
          "suffix to add to {model_name}Validate{suffix}.cfg, when looking for a manual config file",
        default = Some(""),
      )
      val allPaths = toggle(
        descrYes = "explore all paths (as opposed to just one); default = true",
        default = Some(true),
      )
      val progressInv = toggle(
        descrYes = "assert vector clock progress is always possible; default = true",
        default = Some(true),
      )
    }
    addSubcommand(TraceGenCmd)
    object TLCCmd extends Subcommand("tlc"):
      val dfs =
        toggle(descrYes = "enable depth-first search", default = Some(false))
      val tlcArgs =
        trailArg[List[String]](descr = "arguments to forward to TLC")
    addSubcommand(TLCCmd)
    object HarvestTracesCmd extends Subcommand("harvest-traces"):
      val folder =
        trailArg[os.Path](descr = "folder where the system to trace lives")
      val tracesSubFolder = opt[String](
        descr = "subfolder to store generated traces",
        default = Some("traces_found"),
      )
      val tracesNeeded = opt[Int](
        descr = "how many unique traces to discover",
        default = Some(1),
      )
      val disruptionTime = opt[duration.Duration](
        descr = "average time for disruptions",
        default = Some(duration.Duration("100micro")),
      )
      val victimCmd = trailArg[List[String]](descr =
        "command to launch the implementation code, specify after -- (will be launched repeatedly)",
      )
    end HarvestTracesCmd
    addSubcommand(HarvestTracesCmd)

    // one of the subcommands must be passed
    addValidation {
      subcommand match {
        case Some(_) => Right(())
        case None    => Left(s"a subcommand must be given")
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

  def charBufferFromFile(
      file: os.Path,
      use: Using.Manager,
  ): java.nio.CharBuffer = {
    val fileChannel = use(new RandomAccessFile(file.toIO, "r").getChannel)
    val buffer =
      fileChannel.map(FileChannel.MapMode.READ_ONLY, 0, fileChannel.size)
    StandardCharsets.UTF_8.decode(buffer)
  }

  private def parseMPCal(specFile: os.Path): (TLAModule, MPCalBlock) = {
    val underlyingFile = new SourceLocation.UnderlyingFile(specFile)
    Using.Manager { use =>
      val charBuffer = charBufferFromFile(specFile, use = use)

      val tlaModule =
        TLAParser.readModuleBeforeTranslation(underlyingFile, charBuffer)
      val mpcalBlock =
        MPCalParser.readBlock(underlyingFile, charBuffer, tlaModule)
      (tlaModule, mpcalBlock)
    }.get
  }

  private def parsePCal(specFile: os.Path): (TLAModule, PCalAlgorithm) = {
    val underlyingFile = new SourceLocation.UnderlyingFile(specFile)
    Using.Manager { use =>
      val charBuffer = charBufferFromFile(specFile, use = use)

      val tlaModule =
        TLAParser.readModuleBeforeTranslation(underlyingFile, charBuffer)
      val pcalAlgorithm =
        PCalParser.readAlgorithm(underlyingFile, charBuffer, tlaModule)
      (tlaModule, pcalAlgorithm)
    }.get
  }

  sealed abstract class PCalWriteError extends PGoError with PGoError.Error {
    override val errors: List[PGoError.Error] = List(this)
  }
  object PCalWriteError {
    final case class PCalTagsError(err: ParseFailureError)
        extends PCalWriteError {
      initCause(err)

      override val sourceLocation: SourceLocation = err.sourceLocation
      override val description: Description =
        d"one or both of `\\* BEGIN PLUSCAL TRANSLATION` and `\\* END PLUSCAL TRANSLATION` not found, or not found in the correct order;\n" +
          d"add these tags so that PGo knows where to put its generated PlusCal:\n" +
          err.description.indented
    }
  }

  final case class FileSystemError(err: java.nio.file.FileSystemException)
      extends PGoError
      with PGoError.Error {
    initCause(err)

    override val errors: List[PGoError.Error] = List(this)
    override val sourceLocation: SourceLocation = SourceLocation.unknown
    override val description: Description = {
      val reason: Description =
        Option(err.getReason).map(reason => d": $reason").getOrElse(d"")
        + locally:
          val str = StringWriter()
          str.append("\n")
          err.printStackTrace(PrintWriter(str))
          str.toString().description
      val files: List[String] =
        Nil ++ Option(err.getFile) ++ Option(err.getOtherFile)

      val involvingFiles: Description =
        if (files.isEmpty) {
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
          MPCalSemanticCheckPass(
            tlaModule,
            mpcalBlock,
            noMultipleWrites = config.noMultipleWrites(),
          )
          mpcalBlock = MPCalNormalizePass(tlaModule, mpcalBlock)

          val goCode = MPCalGoCodegenPass(
            tlaModule,
            mpcalBlock,
            packageName = config.GoGenCmd.packageName.toOption,
          )
          os.write.over(
            config.GoGenCmd.outFile(),
            goCode.linesIterator.map(line => s"$line\n"),
          )

          val fmtResult = os
            .proc("go", "fmt", config.GoGenCmd.outFile())
            .call(cwd = os.pwd, check = false)
          if (fmtResult.exitCode != 0) {
            println(
              "could not run go fmt on output. this probably isn't fatal, but the Go output might look a little odd",
            )
          }

        case config.PCalGenCmd =>
          var (tlaModule, mpcalBlock) = parseMPCal(config.PCalGenCmd.specFile())
          MPCalSemanticCheckPass(
            tlaModule,
            mpcalBlock,
            noMultipleWrites = config.noMultipleWrites(),
          )
          mpcalBlock = MPCalNormalizePass(tlaModule, mpcalBlock)

          val pcalAlgorithm = MPCalPCalCodegenPass(tlaModule, mpcalBlock)
          val renderedPCal = PCalRenderPass(pcalAlgorithm)

          val tempOutput = os.temp(
            dir = config.PCalGenCmd.specFile() / os.up,
            deleteOnExit = true,
          )
          locally {

            /** A simple parser that splits ("chops") an MPCal-containing TLA+
              * file into 3 parts:
              *   - the bit before the PlusCal translation area
              *   - the PlusCal translation area (which is not returned)
              *   - the bit after the PlusCal translation area
              *
              * the before- and after- parts can be combined with a new PlusCal
              * translation in order to insert a new translation
              */
            object PCalChopParser extends RegexParsers with ParsingUtils {
              override val skipWhitespace: Boolean =
                false // as usual, let us handle all the spacing explicitly

              val ws: Parser[String] = raw"""(?!\n)\s+""".r
              val pcalBeginTranslation: Parser[Unit] =
                ((ws.? ~> "\\*" ~> ws ~> "BEGIN" ~> ws ~> "PLUSCAL" ~> ws ~> "TRANSLATION" ~> ws.? ~> "\n") ^^^ ())
                  .withFailureMessage(
                    "`\\* BEGIN PLUSCAL TRANSLATION`, modulo whitespace, expected",
                  )
              val pcalEndTranslation: Parser[Unit] =
                ((ws.? ~> "\\*" ~> ws ~> "END" ~> ws ~> "PLUSCAL" ~> ws ~> "TRANSLATION" ~> ws.? ~> "\n") ^^^ ())
                  .withFailureMessage(
                    "`\\* END PLUSCAL TRANSLATION`, modulo whitespace, expected",
                  )
              val anyLine: Parser[String] = (rep(
                acceptIf(_ != '\n')(ch => s"'$ch' was a newline'"),
              ) <~ "\n").map(_.mkString)

              val nonMarkerLine: Parser[String] =
                not(pcalBeginTranslation | pcalEndTranslation) ~> anyLine

              val theChop: Parser[(List[String], List[String])] =
                phrase {
                  rep(nonMarkerLine) ~
                    (pcalBeginTranslation ~> rep(
                      nonMarkerLine,
                    ) ~> pcalEndTranslation ~> (rep(nonMarkerLine) ~
                      (not(pcalBeginTranslation | pcalEndTranslation) ~> rep1(
                        acceptIf(_ != '\n')(ch => s"'$ch' was a newline"),
                      ).map(_.mkString).?)))
                } ^^ { case linesBefore ~ (linesAfter ~ lastLine) =>
                  // note: lastLine accounts for cases where a file is not \n-terminated... which happens somewhat often, and
                  //       confuses the line detection method used in anyLine, which relies on all lines having a trailing \n
                  (linesBefore, linesAfter ++ lastLine)
                }

              def parseTheChop(file: os.Path): (List[String], List[String]) = {
                val underlyingText = new SourceLocation.UnderlyingFile(file)
                Using.Manager { use =>
                  val reader =
                    buildReader(charBufferFromFile(file, use), underlyingText)
                  checkResult(theChop(reader))
                }.get
              }
            }

            val renderedPCalIterator =
              Iterator("\\* BEGIN PLUSCAL TRANSLATION") ++
                renderedPCal.linesIterator ++
                Iterator("", "\\* END PLUSCAL TRANSLATION")

            try {
              os.write.over(
                tempOutput,
                PCalChopParser.parseTheChop(
                  config.PCalGenCmd.specFile(),
                ) match {
                  case (beforeLines, afterLines) =>
                    (beforeLines.iterator ++ renderedPCalIterator ++ afterLines.iterator)
                      .flatMap(line => Iterator(line, "\n"))
                },
              )
            } catch {
              case err: ParseFailureError =>
                throw PCalWriteError.PCalTagsError(
                  err,
                ) // wrap error for UI; this is a special parse error
            }
          }

          // move the rendered output over the spec file, replacing it.
          os.move(
            from = tempOutput,
            to = config.PCalGenCmd.specFile(),
            replaceExisting = true,
            atomicMove = true,
          )

          // run a free-standing semantic check on the generated code, in case our codegen doesn't agree with our
          // own semantic checks (which would be a bug!)
          locally {
            try {
              val (tlaModule, pcalAlgorithm) =
                parsePCal(config.PCalGenCmd.specFile())
              MPCalSemanticCheckPass(
                tlaModule,
                MPCalBlock.fromPCalAlgorithm(pcalAlgorithm),
                noMultipleWrites = true,
              )
            } catch {
              case err: PGoError =>
                throw MPCalSemanticCheckPass.SemanticError(
                  err.errors.map(
                    MPCalSemanticCheckPass.SemanticError.ConsistencyCheckFailed.apply,
                  ),
                )
            }
          }

          // Regenerate the TLA+ by running the bundled PCal translator
          pgo.util.TLC.translatePCal(specFile = config.PCalGenCmd.specFile())
        case config.TraceGenCmd =>
          val specFile = config.TraceGenCmd.specFile()
          val destDir = config.TraceGenCmd.destDir()

          val (tlaModule, mpcalBlock) = parseMPCal(specFile)
          val traceConf = tracing
            .InferFromMPCal(
              mpcalBlock = mpcalBlock,
              tlaModule = tlaModule,
              destDir = destDir,
            )
            .withAllPaths(allPaths = config.TraceGenCmd.allPaths())
            .withProgressInv(progressInv = config.TraceGenCmd.progressInv())
          val logFiles = os
            .list(config.TraceGenCmd.logsDir())
            .filter(os.isFile)
            .filter(_.last.endsWith(".log"))

          // utility: copy spec over
          os.copy.over(from = specFile, to = destDir / specFile.last)

          traceConf.generate(logFiles.toList)

          // utility: copy over a hand-written .cfg file
          val cfgFile = config.TraceGenCmd.cfgFile()
          val cfgFileDest =
            destDir / s"${specFile.last.stripSuffix(".tla")}Validate.cfg"
          if os.exists(cfgFile)
          then
            os.write.append(
              target = cfgFileDest,
              data = List("\n", os.read(cfgFile)),
            )
        case config.TLCCmd =>
          val workDir = config.TLCCmd
            .tlcArgs()
            .find(_.endsWith(".tla"))
            .map: specArg =>
              os.Path(specArg, os.pwd) / os.up
            .getOrElse(os.pwd)

          def tryCleanPath(str: String): String =
            try
              os.Path(str, os.pwd).toString
            catch
              case _: IllegalArgumentException => str

          pgo.util.TLC.runTLC(
            workDir,
            javaOpts =
              if config.TLCCmd.dfs() then
                List("-Dtlc2.tool.queue.IStateQueue=StateDeque")
              else Nil,
          )(config.TLCCmd.tlcArgs().map(tryCleanPath))

        case config.HarvestTracesCmd =>
          val folder = config.HarvestTracesCmd.folder()
          val disruptionTime = config.HarvestTracesCmd.disruptionTime()
          val victimCmd = config.HarvestTracesCmd.victimCmd()

          tracing.HarvestTraces(
            folder = folder,
            disruptionTime = disruptionTime,
            tracesSubFolderName = config.HarvestTracesCmd.tracesSubFolder(),
            tracesNeeded = config.HarvestTracesCmd.tracesNeeded(),
            victimCmd = victimCmd,
          )
      }
      Nil
    } catch {
      case err: java.nio.file.FileSystemException =>
        List(FileSystemError(err))
      case err: PGoError =>
        err.errors
          // ensure you don't see the same msg twice
          .distinctBy(e =>
            (e.sourceLocation.longDescription + d"\n" + e.description).linesIterator
              .mkString("\n"),
          )
    }
  }

  def main(args: Array[String]): Unit = {
    val startTime = System.currentTimeMillis()
    val errors = run(ArraySeq.unsafeWrapArray(args))
    val endTime = System.currentTimeMillis()
    val duration = Duration(length = endTime - startTime, unit = MILLISECONDS)
    if (errors.nonEmpty) {
      d"failed in ${duration.toString()}:${errors.view.map(err => d"\n${err.description} at ${err.sourceLocation.longDescription.indented}").flattenDescriptions}".linesIterator
        .foreach(System.err.println)
      sys.exit(1)
    } else {
      System.err.println(s"ok in ${duration.toString()}")
    }
  }
}
