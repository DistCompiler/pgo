 package pgo;

import plume.Option;
import plume.Options;
import org.json.*;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

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

	@Option(value = "-c path to the configuration file, if any")
	public String optsfile = "";

	@Option(value = "write the AST generated and skip the rest", aliases = { "-ast" })
	public boolean writeAST = false;

	public String infile = "";

	// fields extracted from the JSON configuration file
	public String buildDir;
	public String buildFile;
	public PGoNetOptions net;

	private Options plumeOptions;

	private static String usageString = "pgo [options] pcalfile";

	public void printHelp() {
		plumeOptions.print_usage();
	}

	public PGoOptions(String[] args) throws PGoOptionException {
		plumeOptions = new plume.Options(usageString, this);
		String[] remaining_args = plumeOptions.parse_or_usage(args);

		if (optsfile.isEmpty()) {
			throw new PGoOptionException("Configuration file is required");
		}

		if (remaining_args.length == 1) {
			infile = remaining_args[0];
		} else {
			throw new PGoOptionException("Invalid command line parameters");
		}
	}

	public void checkOptions() throws PGoOptionException {
		if (help) {
			printHelp();
			System.exit(0);
		}

		String s;

		try {
			byte[] jsonBytes = Files.readAllBytes(Paths.get(optsfile));
			s = new String(jsonBytes);
		} catch (IOException ex) {
			throw new PGoOptionException("Error reading configuration file: " + ex.getMessage());
		}

		JSONObject config;

		try {
			config = new JSONObject(s);
		} catch (JSONException e) {
			throw new PGoOptionException(optsfile + ": parsing error: " + e.getMessage());
		}

		buildDir = config.getJSONObject("build").getString("output_dir");
		buildFile = config.getJSONObject("build").getString("dest_file");
		net = new PGoNetOptions(config);

		return;
	}
}
