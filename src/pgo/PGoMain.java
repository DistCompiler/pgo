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

	private static Logger logger;
	private PGoOptions opts = null;
	private static PGoMain instance = null;

	// Check options, sets up logging.
	public PGoMain(String[] args) throws PGoOptionException {
		opts = new PGoOptions(args);
		try {
			opts.checkOptions();
		} catch (PGoOptionException e) {
			logger.severe(e.getMessage());
			opts.printHelp();
			System.exit(-1);
		}

		// set up logging with correct verbosity
		setUpLogging(opts);
	}

	// Creates a PGoMain instance, and initiates run() below.
	public static void main(String[] args) {
		// Get the top Logger instance
		logger = Logger.getLogger("PGoMain");

		try {
			instance = new PGoMain(args);
		} catch (PGoOptionException e) {
			logger.severe(e.getMessage());
			System.exit(-1);
		}

		instance.run();
		logger.info("Finished");
	}

	// Top-level workhorse method.
	public void run() {
		PcalParser parser = new PcalParser(opts.infile);

		ParsedPcal pcal;
		try {
			pcal = parser.parse();
		} catch (PGoParseException e) {
			logger.severe(e.getMessage());
			return;
		}

		// for -writeAST option, just write the file AST.tla and halt.
		if (opts.writeAST) {
			IOUtil.WriteAST(pcal.getAST(), opts.buildDir + "/" + opts.buildFile);
			return; // added for testing
		}

		try {
			TopLevelIssueContext ctx = new TopLevelIssueContext();
			TLAModuleLoader loader = new TLAModuleLoader(Collections.singletonList(Paths.get(opts.infile).getParent()));

			logger.info("Parsing TLA+ module");
			PGoTLAModule tlaModule = TLAParsingPass.perform(ctx, Paths.get(opts.infile));
			checkErrors(ctx);

			logger.info("Cleaning up PlusCal AST");
			Algorithm pcalAlgorithm = PlusCalConversionPass.perform(ctx, pcal);
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
			DefinitionRegistry registry = PGoScopingPass.perform(ctx, tlaModule, pcalAlgorithm, loader);
			checkErrors(ctx);

			logger.info("Inferring types");
			Map<UID, PGoType> typeMap = TypeInferencePass.perform(ctx, registry, pcalAlgorithm);
			checkErrors(ctx);

			System.out.println(typeMap);

			/*logger.info("Entering Stage Four: Inferring atomicity constraints");
			PGoTransStageAtomicity s4 = new PGoTransStageAtomicity(s3);
			logger.info("Entering Stage Five: Generating Go AST");
			PGoTransStageGoGen s5 = new PGoTransStageGoGen(s4);
			logger.info("Entering Stage Six: Generating Go Code");*/
			logger.info("Writing Go to \"" + opts.buildFile + "\" in folder \"" + opts.buildDir + "\"");
			IOUtil.WriteStringVectorToFile(getGoLines(), opts.buildDir + "/" + opts.buildFile);
			logger.info("Copying necessary Go packages to folder \"" + opts.buildDir + "\"");
			copyPackages(opts);

			logger.info("Formatting generated Go code");
			try {
				goFmt();
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

	private static void copyPackages(PGoOptions opts) throws IOException {
		FileUtils.copyDirectory(new File("src/go/pgo"), new File(opts.buildDir + "/src/pgo"));
		FileUtils.copyDirectory(new File("src/go/github.com/emirpasic"),
				new File(opts.buildDir + "/src/github.com/emirpasic"));
	}

	private static void setUpLogging(PGoOptions opts) {
		// Set the logger's log level based on command line arguments
		if (opts.logLvlQuiet) {
			logger.setLevel(Level.WARNING);
		} else if (opts.logLvlVerbose) {
			logger.setLevel(Level.FINE);
		} else {
			logger.setLevel(Level.INFO);
		}
	}

	private void goFmt() throws IOException, InterruptedException {
		String destFile = String.format("%s/%s", opts.buildDir, opts.buildFile);
		String command = String.format("gofmt -w %s", destFile);

		Process p = Runtime.getRuntime().exec(command);
		p.waitFor();
	}

}
