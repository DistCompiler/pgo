package pgo;

import plume.Option;
import plume.Options;

public class PGoOptions {

	@Option(value = "-h Print usage information", aliases = { "-help" })
	public boolean help = false;

	@Option(value = "-q Reduce printing during execution", aliases = { "-quiet" })
	public boolean logLvlQuiet = false;

	/**
	 * Be verbose, print extra detailed information. Sets the log level to FINE.
	 */
	@Option(value = "-v Print detailed information during execution ", aliases = { "-verbose" })
	public boolean logLvlVerbose = false;

	@Option(value = "-i the input pluscal file to transpile ")
	public static String pcalfile = "";

	@Option(value = "-o the output golang file to generate")
	public static String gofile = "";

	@Option(value = "write the AST generated and skip the rest", aliases = { "-ast" })
	public static boolean writeAST = false;

	private Options plumeOptions;

	private static String kUsageString = "pgo [options] pcalfile gofile";

	public PGoOptions(String[] args) throws PGoOptionException {
		plumeOptions = new plume.Options(kUsageString, this);
		String[] remaining_args = plumeOptions.parse_or_usage(args);

		if (remaining_args.length > 0) {
			if (!pcalfile.isEmpty() || !gofile.isEmpty()) {
				throw new PGoOptionException("PlusCal input or Go output file specified twice");
			}

			pcalfile = remaining_args[0];
			if (remaining_args.length == 2) {
				gofile = remaining_args[1];
			}
		}

		checkOptions();
	}

	private void checkOptions() throws PGoOptionException {
		if (pcalfile.isEmpty()) {
			throw new PGoOptionException("Input pluscal file is not specified");
		}
		if (!writeAST) {
			if (gofile.isEmpty()) {
				throw new PGoOptionException("Output go file is not specified");
			}
		}

		return;
	}
}
