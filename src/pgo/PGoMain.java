package pgo;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.CharBuffer;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.Map;
import java.util.logging.Logger;

import org.apache.commons.io.FileUtils;
import pcal.exception.StringVectorToFileException;
import pgo.errors.TopLevelIssueContext;
import pgo.model.golang.Module;
import pgo.model.pcal.Algorithm;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLAModule;
import pgo.model.type.PGoType;
import pgo.modules.TLAModuleLoader;
import pgo.scope.UID;
import pgo.trans.PGoTransException;
import pgo.trans.intermediate.*;
import pgo.trans.passes.constdef.ConstantDefinitionParsingPass;
import pgo.trans.passes.tlaparse.TLAParsingPass;
import pgo.trans.passes.type.TypeInferencePass;
import pgo.util.IOUtil;

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

			logger.info("Reading lines from source file");
			Path inputFilePath = Paths.get(opts.inputFilePath);
			FileChannel fileChannel = new RandomAccessFile(inputFilePath.toFile(), "r").getChannel();
			MappedByteBuffer buffer = fileChannel.map(FileChannel.MapMode.READ_ONLY, 0, fileChannel.size());
			// assume UTF-8, though technically TLA+ is ASCII only according to the book
			CharBuffer inputFileContents = StandardCharsets.UTF_8.decode(buffer);

			logger.info("Parsing PlusCal code");
			Algorithm algorithm = PlusCalParsingPass.perform(ctx, inputFilePath, inputFileContents);
			checkErrors(ctx);

			// for -writeAST option, just write the file AST.tla and halt.
			/*if (opts.writeAST) {
				IOUtil.WriteAST(pCalAST, opts.buildDir + "/" + opts.buildFile);
				return true; // added for testing
			}*/

			logger.info("Parsing TLA+ module");
			PGoTLAModule tlaModule = TLAParsingPass.perform(ctx, inputFilePath, inputFileContents);
			checkErrors(ctx);

			logger.info("Parsing constant definitions from configuration");
			Map<String, PGoTLAExpression> constantDefinitions = ConstantDefinitionParsingPass.perform(
					ctx, opts.constants.getConstants());
			checkErrors(ctx);

			logger.info("Checking compile options for sanity");
			CheckOptionsPass.perform(ctx, algorithm, opts);
			checkErrors(ctx);

			logger.info("Expanding PlusCal macros");
			algorithm = PlusCalMacroExpansionPass.perform(ctx, algorithm);
			checkErrors(ctx);

			logger.info("Resolving TLA+ and PlusCal scoping");
			TLAModuleLoader loader = new TLAModuleLoader(Collections.singletonList(inputFilePath.getParent()));
			DefinitionRegistry registry = PGoScopingPass.perform(ctx, tlaModule, algorithm, loader, constantDefinitions);
			checkErrors(ctx);

			logger.info("Inferring types");
			Map<UID, PGoType> typeMap = TypeInferencePass.perform(ctx, registry, algorithm);
			checkErrors(ctx);

			logger.info("Inferring atomicity requirements");
			AtomicityInferencePass.perform(registry, algorithm);

			logger.info("Initial code generation");
			Module module = CodeGenPass.perform(registry, typeMap, opts, algorithm);

			logger.info("Normalising generated code");
			Module normalisedModule = CodeNormalisingPass.perform(module);

			logger.info("Writing Go to \"" + opts.buildFile + "\" in folder \"" + opts.buildDir + "\"");
			IOUtil.WriteStringVectorToFile(Collections.singletonList(normalisedModule.toString()), opts.buildDir + "/" + opts.buildFile);
			logger.info("Copying necessary Go packages to folder \"" + opts.buildDir + "\"");
			copyPackages(opts.buildDir);

			logger.info("Formatting generated Go code");
			try {
				goFmt(opts.buildDir + "/" + opts.buildFile);
			} catch (Exception e) {
				logger.warning(String.format("Failed to format Go code. Error: %s", e.getMessage()));
			}
			return true;

		} catch (PGoTransException | StringVectorToFileException | IOException e) {
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
