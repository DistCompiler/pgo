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
	public String infile = "";

	@Option(value = "-o the output file to generate")
	public String outfile = "";

	@Option(value = "-d the output folder to put additional packages")
	public String outfolder = "";

	@Option(value = "write the AST generated and skip the rest", aliases = { "-ast" })
	public boolean writeAST = false;

	private Options plumeOptions;

	private static String kUsageString = "pgo [options] pcalfile gofolder gofile";

	public void printHelp() {
		plumeOptions.print_usage();
	}

	public PGoOptions(String[] args) throws PGoOptionException {
		plumeOptions = new plume.Options(kUsageString, this);
		String[] remaining_args = plumeOptions.parse_or_usage(args);

		if (remaining_args.length > 0) {
			if (!infile.isEmpty() || !outfolder.isEmpty() || !outfile.isEmpty()) {
				throw new PGoOptionException("PlusCal input or Go output file specified twice");
			}

			infile = remaining_args[0];
			if (remaining_args.length == 3) {
				outfolder = remaining_args[1];
				outfile = remaining_args[2];
			}
		}
	}

	public void checkOptions() throws PGoOptionException {
		if (help) {
			printHelp();
			System.exit(0);
		}

		if (infile.isEmpty()) {
			throw new PGoOptionException("Input pluscal file is not specified");
		}

		if (outfolder.isEmpty()) {
			throw new PGoOptionException("Output go folder is not specified");
		}

		if (outfile.isEmpty()) {
			throw new PGoOptionException("Output go file is not specified");
		}

		return;
	}
}
