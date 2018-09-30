package pgo;

import org.apache.commons.io.FileUtils;
import pgo.errors.TopLevelIssueContext;
import pgo.formatters.GoNodeFormattingVisitor;
import pgo.formatters.IndentingWriter;
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
import pgo.trans.passes.codegen.CodeGenPass;
import pgo.trans.passes.constdef.ConstantDefinitionParsingPass;
import pgo.trans.passes.expansion.ModularPlusCalExpansionPass;
import pgo.trans.passes.mpcal.ModularPlusCalParsingPass;
import pgo.trans.passes.mpcal.ModularPlusCalValidationPass;
import pgo.trans.passes.scope.pluscal.PlusCalScopingPass;
import pgo.trans.passes.scope.tla.TLAScopingPass;
import pgo.trans.passes.scope.mpcal.ModularPlusCalScopingPass;
import pgo.trans.passes.tlaparse.TLAParsingPass;
import pgo.trans.passes.type.TypeInferencePass;

import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.CharBuffer;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
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

			logger.info("Parsing constant definitions from configuration");
			Map<String, TLAExpression> constantDefinitions = ConstantDefinitionParsingPass.perform(
					ctx, opts.constants.getConstants());
			checkErrors(ctx);

			logger.info("Checking compile options for sanity");
			CheckOptionsPass.perform(ctx, modularPlusCalBlock, opts);
			checkErrors(ctx);

			logger.info("Resolving TLA+ scoping");
			TLAModuleLoader loader = new TLAModuleLoader(Collections.singletonList(inputFilePath.getParent()));
			DefinitionRegistry registry = new DefinitionRegistry();
			TLAScopeBuilder tlaScope = TLAScopingPass.perform(ctx, registry, loader, constantDefinitions, tlaModule);
			checkErrors(ctx);

			logger.info("Resolve Modular PlusCal scoping");
			TLAScopeBuilder modularPlusCalScope = ModularPlusCalScopingPass.perform(
					ctx, registry, loader, tlaScope, modularPlusCalBlock);
			checkErrors(ctx);

			logger.info("Validating " + (isMPCal ? "Modular PlusCal" : "PlusCal") +  " semantics");
			ModularPlusCalValidationPass.perform(ctx, modularPlusCalBlock);
			checkErrors(ctx);

			String msg = "Expanding PlusCal macros";
			if (isMPCal) {
				msg += " and Modular PlusCal instances";
			}
			logger.info(msg);
			ModularPlusCalBlock expandedModularPlusCalBlock = ModularPlusCalExpansionPass.perform(
					ctx, modularPlusCalBlock);
			checkErrors(ctx);

			logger.info("Resolving PlusCal scoping");
			PlusCalScopingPass.perform(
					ctx, registry, loader, tlaScope, modularPlusCalScope, expandedModularPlusCalBlock);
			checkErrors(ctx);

			logger.info("Inferring types");
			Map<UID, PGoType> typeMap = TypeInferencePass.perform(ctx, registry, expandedModularPlusCalBlock);
			checkErrors(ctx);

			logger.info("Inferring atomicity requirements");
			AtomicityInferencePass.perform(registry, expandedModularPlusCalBlock);

			if (opts.mpcalCompile) {
				// compilation of MPCal -> PCal
				throw new UnsupportedOperationException("Generation of PCal specs from MPCal currently unsupported");

			} else if (isMPCal) {
				// compilation of MPCal -> Go
				throw new UnsupportedOperationException("Compilation of MPCal specs currently unsupported");

			} else {
				// compilation of PCal -> Go
				logger.info("Initial code generation");
				GoModule goModule = CodeGenPass.perform(registry, typeMap, opts, expandedModularPlusCalBlock);

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
			logger.severe(e.getMessage());
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
