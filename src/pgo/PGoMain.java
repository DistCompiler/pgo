package pgo;

import java.util.logging.Level;
import java.util.logging.Logger;

import pcal.exception.StringVectorToFileException;
import pgo.parser.PGoParseException;
import pgo.parser.PcalParser;
import pgo.parser.PcalParser.ParsedPcal;
import pgo.trans.PGoTransException;
import pgo.trans.PGoTranslater;
import pgo.util.IOUtil;

// TODO refactor this mess
public class PGoMain {

	private static Logger logger;

	private PGoOptions opts = null;
	private static PGoMain instance = null;

	public PGoMain(String[] args) throws PGoOptionException {
		opts = new PGoOptions(args);

		// set up logging with correct verbosity
		setUpLogging(opts);
	}

	public static void main(String[] args) {
		// Get the top Logger instance
		logger = Logger.getLogger("PGoMain");

		try {
			instance = new PGoMain(args);
		} catch (PGoOptionException e) {
			logger.severe(e.getMessage());
		}

		instance.run();
	}

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
			IOUtil.WriteAST(pcal.getAST(), opts.outfile);
			return; // added for testing
		}
		
		try {
			PGoTranslater trans = new PGoTranslater(pcal);
			logger.info("Writing Go to \"" + opts.outfile + "\"");
			IOUtil.WriteStringVectorToFile(trans.getLines(), opts.outfile);
		} catch (PGoTransException | PGoParseException | StringVectorToFileException e) {
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
