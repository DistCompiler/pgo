package pgo;

import org.apache.commons.io.FileUtils;
import pgo.errors.TopLevelIssueContext;
import pgo.formatters.GoNodeFormattingVisitor;
import pgo.formatters.IndentingWriter;
import pgo.formatters.PlusCalNodeFormattingVisitor;
import pgo.model.golang.GoModule;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.PlusCalAlgorithm;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAModule;
import pgo.model.type.PGoType;
import pgo.modules.TLAModuleLoader;
import pgo.scope.UID;
import pgo.trans.PGoTransException;
import pgo.trans.intermediate.*;
import pgo.trans.passes.codegen.go.GoCodeGenPass;
import pgo.trans.passes.constdef.ConstantDefinitionParsingPass;
import pgo.trans.passes.codegen.pluscal.PlusCalCodeGenPass;
import pgo.trans.passes.expansion.ModularPlusCalMacroExpansionPass;
import pgo.trans.passes.parse.mpcal.ModularPlusCalParsingPass;
import pgo.trans.passes.parse.mpcal.ModularPlusCalValidationPass;
import pgo.trans.passes.scope.ScopingPass;
import pgo.trans.passes.parse.tla.TLAParsingPass;

import java.io.*;
import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.logging.Logger;

public class PGoMain {
	private String[] cmdArgs;
	private static Logger logger;

	public PGoMain(String[] args) {
		cmdArgs = args;
	}

	// Creates a PGoMain instance, and initiates run() below.
	public static void main(String[] args) {
		// Get the top Logger instance
		logger = Logger.getLogger("PGoMain");
		if(new PGoMain(args).run()) {
			logger.info("Finished");
		}else {
			logger.info("Terminated with errors");
		}
	}

	// Top-level workhorse method.
	public boolean run() {
		try {
			TopLevelIssueContext ctx = new TopLevelIssueContext();

			// Check options, set up logging.
			PGoOptions opts = OptionParsingPass.perform(ctx, logger, cmdArgs);
			if (ctx.hasErrors()) {
				System.err.println(ctx.format());
				opts.printHelp();
				return false;
			}

			logger.info("Opening source file");
			Path inputFilePath = Paths.get(opts.inputFilePath);
			final boolean isMPCal;
			final ModularPlusCalBlock modularPlusCalBlock;
			final TLAModule tlaModule;

			try (FileChannel fileChannel = new RandomAccessFile(inputFilePath.toFile(), "r").getChannel()) {
				MappedByteBuffer buffer = fileChannel.map(FileChannel.MapMode.READ_ONLY, 0, fileChannel.size());
				// assume UTF-8, though technically TLA+ is ASCII only according to the book
				CharBuffer inputFileContents = StandardCharsets.UTF_8.decode(buffer);

				isMPCal = ModularPlusCalParsingPass.hasModularPlusCalBlock(inputFilePath, inputFileContents);
				if (opts.mpcalCompile && !isMPCal) {
					ctx.error(new OptionParserIssue("Specification does not contain a Modular PlusCal block."));
					checkErrors(ctx);
				}

				if (isMPCal) {
					logger.info("Parsing modular PlusCal code");
					modularPlusCalBlock = ModularPlusCalParsingPass.perform(ctx, inputFilePath, inputFileContents);
					checkErrors(ctx);
				} else {
					logger.info("Parsing PlusCal code");
					final PlusCalAlgorithm plusCalAlgorithm = PlusCalParsingPass.perform(
							ctx, inputFilePath, inputFileContents);
					checkErrors(ctx);
					modularPlusCalBlock = ModularPlusCalBlock.from(plusCalAlgorithm);
				}

				logger.info("Parsing TLA+ module");
				tlaModule = TLAParsingPass.perform(ctx, inputFilePath, inputFileContents);
				checkErrors(ctx);
			}

			Map<String, TLAExpression> constantDefinitions = new HashMap<>();

			// check compilation options if we are compiling to an implementation
			if (!opts.mpcalCompile) {
				logger.info("Parsing constant definitions from configuration");
				constantDefinitions = ConstantDefinitionParsingPass.perform(
						ctx, opts.constants.getConstants());
				checkErrors(ctx);

				logger.info("Checking compile options for sanity");
				CheckOptionsPass.perform(ctx, modularPlusCalBlock, opts);
				checkErrors(ctx);
			}

			logger.info("Validating " + (isMPCal ? "Modular PlusCal" : "PlusCal") +  " semantics");
			ModularPlusCalValidationPass.perform(ctx, modularPlusCalBlock);
			checkErrors(ctx);

			String msg = "Expanding PlusCal macros";
			if (isMPCal) {
				msg += " and Modular PlusCal instances";
			}
			logger.info(msg);
			ModularPlusCalBlock macroExpandedModularPlusCalBlock = ModularPlusCalMacroExpansionPass.perform(
					ctx, modularPlusCalBlock);
			checkErrors(ctx);

			logger.info("Resolving scopes");
			TLAModuleLoader loader = new TLAModuleLoader(Collections.singletonList(inputFilePath.getParent()));
			DefinitionRegistry registry = ScopingPass.perform(
					ctx, isMPCal, loader, constantDefinitions, tlaModule, macroExpandedModularPlusCalBlock);
			checkErrors(ctx);

			logger.info("Inferring types");
			Map<UID, PGoType> typeMap = new HashMap<>();// TypeInferencePass.perform(ctx, registry, macroExpandedModularPlusCalBlock);
			checkErrors(ctx);

			logger.info("Inferring atomicity requirements");
			AtomicityInferencePass.perform(registry, macroExpandedModularPlusCalBlock);

			if (opts.mpcalCompile) {
				// compilation of MPCal -> PCal
				logger.info("Generating PlusCal code");
				StringWriter output = new StringWriter();
				try (IndentingWriter out = new IndentingWriter(output)) {
					PlusCalAlgorithm algorithm = PlusCalCodeGenPass.perform(ctx, registry, macroExpandedModularPlusCalBlock);
					checkErrors(ctx);
					algorithm.accept(new PlusCalNodeFormattingVisitor(out));
				}
				// TODO deal with non-ASCII
				final int startOffset;
				final int endOffset;
				// parse the algorithm block to know where it is
				try (
						FileChannel fileChannel = new RandomAccessFile(inputFilePath.toFile(), "r")
								.getChannel()
				) {
					MappedByteBuffer buffer = fileChannel.map(
							FileChannel.MapMode.READ_ONLY, 0, fileChannel.size());
					// assume UTF-8, though technically TLA+ is ASCII only according to the book
					CharBuffer inputFileContents = StandardCharsets.UTF_8.decode(buffer);
					if (PlusCalParsingPass.hasAlgorithmBlock(inputFilePath, inputFileContents)) {
						final PlusCalAlgorithm plusCalAlgorithm = PlusCalParsingPass.perform(
								ctx, inputFilePath, inputFileContents);
						if (ctx.hasErrors()) {
							startOffset = -1;
							endOffset = -1;
						} else {
							startOffset = plusCalAlgorithm.getLocation().getStartOffset();
							endOffset = plusCalAlgorithm.getLocation().getEndOffset();
						}
					} else {
						startOffset = -1;
						endOffset = -1;
					}
				}
				File tempFile = File.createTempFile("pluscal-", ".tla");
				tempFile.deleteOnExit();
				try (
						FileChannel source = new RandomAccessFile(inputFilePath.toFile(), "r").getChannel();
						FileChannel destination = new RandomAccessFile(tempFile, "rw").getChannel()
				) {
					if (startOffset != -1) {
						long pos = destination.transferFrom(source, 0, startOffset);
						pos += destination.write(StandardCharsets.UTF_8.encode(output.toString()), startOffset);
						pos += destination.transferFrom(source.position(endOffset), pos, source.size() - endOffset);
						destination.truncate(pos);
					} else {
						final int blockEndOffset = modularPlusCalBlock.getLocation().getEndOffset();
						long pos = destination.transferFrom(source, 0, blockEndOffset);
						pos += destination.write(StandardCharsets.UTF_8.encode("\n\n(* "), pos);
						pos += destination.write(StandardCharsets.UTF_8.encode(output.toString()), pos);
						pos += destination.write(StandardCharsets.UTF_8.encode("\n*)\n\n"), pos);
						pos += destination.transferFrom(
								source.position(blockEndOffset),
								pos,
								source.size() - blockEndOffset);
						destination.truncate(pos);
					}
				}
				Files.move(tempFile.toPath(), inputFilePath, StandardCopyOption.REPLACE_EXISTING);
				return true;
			} else if (isMPCal) {
				// compilation of MPCal -> Go
				throw new UnsupportedOperationException("Compilation of MPCal specs currently unsupported");

			} else {
				// compilation of PCal -> Go
				logger.info("Initial code generation");
				GoModule goModule = GoCodeGenPass.perform(registry, typeMap, opts, macroExpandedModularPlusCalBlock);

				logger.info("Normalising generated code");
				GoModule normalisedGoModule = CodeNormalisingPass.perform(goModule);

				logger.info("Writing Go module to \"" + opts.buildFile + "\" in folder \"" + opts.buildDir + "\"");
				try(
						BufferedWriter writer = Files.newBufferedWriter(Paths.get(opts.buildDir+"/"+opts.buildFile));
						IndentingWriter out = new IndentingWriter(writer)
				) {
					normalisedGoModule.accept(new GoNodeFormattingVisitor(out));
				}

				logger.info("Copying necessary Go packages to folder \"" + opts.buildDir + "\"");
				copyPackages(opts.buildDir);

				logger.info("Formatting generated Go code");
				try {
					goFmt(opts.buildDir + "/" + opts.buildFile);
				} catch (Exception e) {
					logger.warning(String.format("Failed to format Go code. Error: %s", e.getMessage()));
				}
				return true;
			}
		} catch (PGoTransException | IOException e) {
			logger.severe("found issues");
			e.printStackTrace();
			return false;
		}
	}

	private static void checkErrors(TopLevelIssueContext ctx) throws PGoTransException {
		if (ctx.hasErrors()) {
			throw new PGoTransException(ctx.format());
		}
	}

	private static void copyPackages(String buildDir) throws IOException {
		FileUtils.copyDirectory(new File("src/runtime/pgo"), new File(buildDir + "/src/pgo"));
	}

	private void goFmt(String... files) throws IOException, InterruptedException {
		String command = "gofmt -w " + String.join(" ", files);
		Process p = Runtime.getRuntime().exec(command);
		p.waitFor();
	}
}
