package pgo.trans.passes.parse.option;

import pgo.PGoOptionException;
import pgo.PGoOptions;
import pgo.errors.IssueContext;

import java.util.logging.Level;
import java.util.logging.Logger;

public class OptionParsingPass {
	private OptionParsingPass() {}

	public static PGoOptions perform(IssueContext ctx, Logger logger, String[] args) {
		PGoOptions opts = new PGoOptions(args);
		try {
			opts.parse();
		} catch (PGoOptionException e) {
			ctx.error(new OptionParserIssue(e.getMessage()));
		}
		// set the logger's log level based on command line arguments
		if (opts.logLvlQuiet) {
			logger.setLevel(Level.WARNING);
		} else if (opts.logLvlVerbose) {
			logger.setLevel(Level.FINE);
		} else {
			logger.setLevel(Level.INFO);
		}
		return opts;
	}
}
