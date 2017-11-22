package pgo;

import java.io.IOException;
import java.util.logging.Level;
import java.util.logging.Logger;

import pcal.exception.StringVectorToFileException;
import pgo.parser.PGoParseException;
import pgo.parser.PcalParser;
import pgo.parser.PcalParser.ParsedPcal;
import pgo.trans.PGoTransException;
import pgo.trans.PGoTranslator;
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
			PGoTranslator trans = new PGoTranslator(pcal, opts.net);
			logger.info("Writing Go to \"" + opts.buildFile + "\" in folder \"" + opts.buildDir + "\"");
			IOUtil.WriteStringVectorToFile(trans.getGoLines(), opts.buildDir + "/" + opts.buildFile);
			logger.info("Copying necessary Go packages to folder \"" + opts.buildDir + "\"");
			trans.copyPackages(opts);
		} catch (PGoTransException | PGoParseException | StringVectorToFileException | IOException e) {
			logger.severe(e.getMessage());
			e.printStackTrace();
		}
	}

	public static void setUpLogging(PGoOptions opts) {
		// Set the logger's log level based on command line arguments
		if (opts.logLvlQuiet) {
			logger.setLevel(Level.WARNING);
		} else if (opts.logLvlVerbose) {
			logger.setLevel(Level.FINE);
		} else {
			logger.setLevel(Level.INFO);
		}
		return;
	}

}
