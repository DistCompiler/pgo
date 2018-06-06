package pgo;

import java.io.File;
import java.io.IOException;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.apache.commons.io.FileUtils;
import pcal.exception.StringVectorToFileException;
import pgo.model.golang.GoProgram;
import pgo.parser.PGoParseException;
import pgo.parser.PcalParser;
import pgo.parser.PcalParser.ParsedPcal;
import pgo.trans.PGoTransException;
import pgo.trans.intermediate.*;
import pgo.util.IOUtil;

public class PGoMain {

	private static Logger logger;
	private PGoOptions opts;
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
		PcalParser parser = new PcalParser(opts.inputFilePath);

		/*********************************************************************
		 * For -writeAST option, just write the file AST.tla and halt. *
		 *********************************************************************/
		ParsedPcal pcal;
		try {
			pcal = parser.parse();
		} catch (PGoParseException e) {
			logger.severe(e.getMessage());
			return;
		}

		if (opts.writeAST) {
			IOUtil.WriteAST(pcal.getAST(), opts.buildDir +"/"+ opts.buildFile);
			return; // added for testing
		}

		try {
			logger.info("Entering Stage One: Inferring intermediate data structures");
			PGoTransStageInitParse s1 = new PGoTransStageInitParse(pcal, opts.net);
			logger.info("Entering Stage Two: Parsing TLA expressions");
			PGoTransStageTLAParse s2 = new PGoTransStageTLAParse(s1);
			logger.info("Entering Stage Three: Inferring types");
			PGoTransStageType s3 = new PGoTransStageType(s2);
			logger.info("Entering Stage Four: Inferring atomicity constraints");
			PGoTransStageAtomicity s4 = new PGoTransStageAtomicity(s3);
			logger.info("Entering Stage Five: Generating Go AST");
			PGoTransStageGoGen s5 = new PGoTransStageGoGen(s4);
			logger.info("Entering Stage Six: Generating Go Code");
			GoProgram go = s5.getGo();
			logger.info("Writing Go to \"" + opts.buildFile + "\" in folder \"" + opts.buildDir + "\"");
			IOUtil.WriteStringVectorToFile(go.toGo(), opts.buildDir + "/" + opts.buildFile);
			logger.info("Copying necessary Go packages to folder \"" + opts.buildDir + "\"");
			copyPackages(opts);

			logger.info("Formatting generated Go code");
			try {
				goFmt();
			} catch (Exception e) {
				logger.warning(String.format("Failed to format Go code. Error: %s", e.getMessage()));
			}

		} catch (PGoTransException | PGoParseException | StringVectorToFileException | IOException e) {
			logger.severe(e.getMessage());
			e.printStackTrace();
		}
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

	private static void copyPackages(PGoOptions opts) throws IOException {
		FileUtils.copyDirectory(new File("src/runtime/pgo"), new File(opts.buildDir + "/src/pgo"));
		FileUtils.copyDirectory(new File("src/runtime/github.com/emirpasic"),
				new File(opts.buildDir + "/src/github.com/emirpasic"));
	}

	private void goFmt() throws IOException, InterruptedException {
		String destFile = String.format("%s/%s", opts.buildDir, opts.buildFile);
		String command = String.format("gofmt -w %s", destFile);

		Process p = Runtime.getRuntime().exec(command);
		p.waitFor();
	}

}
