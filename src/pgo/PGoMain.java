package pgo;

import java.io.File;
import java.io.IOException;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.apache.commons.io.FileUtils;
import pcal.exception.StringVectorToFileException;
import pgo.errors.TopLevelIssueContext;
import pgo.model.golang.Module;
import pgo.model.pcal.Algorithm;
import pgo.model.tla.PGoTLAModule;
import pgo.model.type.PGoType;
import pgo.modules.TLAModuleLoader;
import pgo.parser.PGoParseException;
import pgo.parser.PcalParser;
import pgo.parser.PcalParser.ParsedPcal;
import pgo.scope.UID;
import pgo.trans.PGoTransException;
import pgo.trans.intermediate.*;
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
		new PGoMain(args).run();
		logger.info("Finished");
	}

	// Top-level workhorse method.
	public void run() {
		try {
			TopLevelIssueContext ctx = new TopLevelIssueContext();

			// Check options, set up logging.
			PGoOptions opts = OptionParsingPass.perform(ctx, logger, cmdArgs);
			if (ctx.hasErrors()) {
				System.err.println(ctx.format());
				opts.printHelp();
				System.exit(1);
			}

			logger.info("Parsing PlusCal code");
			ParsedPcal pcal = PlusCalParsingPass.perform(ctx, Paths.get(opts.inputFilePath));
			checkErrors(ctx);

			// for -writeAST option, just write the file AST.tla and halt.
			if (opts.writeAST) {
				IOUtil.WriteAST(pcal.getAST(), opts.buildDir + "/" + opts.buildFile);
				return; // added for testing
			}

			logger.info("Cleaning up PlusCal AST");
			Algorithm pcalAlgorithm = PlusCalConversionPass.perform(ctx, pcal);
			checkErrors(ctx);

			logger.info("Parsing TLA+ module");
			PGoTLAModule tlaModule = TLAParsingPass.perform(ctx, Paths.get(opts.inputFilePath));
			checkErrors(ctx);

			/*logger.info("Parsing PGo annotations");
			PGoAnnotationParser annotations = AnnotationParsingPass.perform(pcal);
			checkErrors(ctx);*/

			logger.info("Checking compile options for sanity");
			CheckOptionsPass.perform(ctx, pcalAlgorithm, opts);
			checkErrors(ctx);

			logger.info("Expanding PlusCal macros");
			pcalAlgorithm = PlusCalMacroExpansionPass.perform(ctx, pcalAlgorithm);
			checkErrors(ctx);

			logger.info("Resolving TLA+ and PlusCal scoping");
			TLAModuleLoader loader = new TLAModuleLoader(Collections.singletonList(Paths.get(opts.inputFilePath).getParent()));
			DefinitionRegistry registry = PGoScopingPass.perform(ctx, tlaModule, pcalAlgorithm, loader);
			checkErrors(ctx);

			logger.info("Inferring types");
			Map<UID, PGoType> typeMap = TypeInferencePass.perform(ctx, registry, pcalAlgorithm);
			checkErrors(ctx);

			Module module = CodeGenPass.perform(pcalAlgorithm, registry, typeMap);

			System.out.println(module);

			/*logger.info("Entering Stage Four: Inferring atomicity constraints");
			PGoTransStageAtomicity s4 = new PGoTransStageAtomicity(s3);
			logger.info("Entering Stage Five: Generating Go AST");
			PGoTransStageGoGen s5 = new PGoTransStageGoGen(s4);
			logger.info("Entering Stage Six: Generating Go Code");*/
			logger.info("Writing Go to \"" + opts.buildFile + "\" in folder \"" + opts.buildDir + "\"");
			IOUtil.WriteStringVectorToFile(getGoLines(), opts.buildDir + "/" + opts.buildFile);
			logger.info("Copying necessary Go packages to folder \"" + opts.buildDir + "\"");
			copyPackages(opts.buildDir);

			logger.info("Formatting generated Go code");
			try {
				goFmt(opts.buildDir + "/" + opts.buildFile);
			} catch (Exception e) {
				logger.warning(String.format("Failed to format Go code. Error: %s", e.getMessage()));
			}

		} catch (PGoTransException | StringVectorToFileException | IOException e) {
			logger.severe(e.getMessage());
			e.printStackTrace();
		}
	}

	private static void checkErrors(TopLevelIssueContext ctx) throws PGoTransException {
		if (ctx.hasErrors()) {
			throw new PGoTransException(ctx.format());
		}
	}

	private static List<String> getGoLines() {
		return null; // TODO
	}

	private static void copyPackages(String buildDir) throws IOException {
		FileUtils.copyDirectory(new File("src/go/pgo"), new File(buildDir + "/src/pgo"));
		FileUtils.copyDirectory(new File("src/go/github.com/emirpasic"),
				new File(buildDir + "/src/github.com/emirpasic"));
	}

	private void goFmt(String... files) throws IOException, InterruptedException {
		String command = "gofmt -w " + String.join(" ", files);
		Process p = Runtime.getRuntime().exec(command);
		p.waitFor();
	}
}
