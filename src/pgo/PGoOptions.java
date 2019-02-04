package pgo;

import org.json.JSONException;
import org.json.JSONObject;
import plume.Option;
import plume.Options;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

public class PGoOptions {
	public static final String VERSION = "0.1.2";

	@Option(value = "Version", aliases = {"-version"})
	public boolean version = false;

	@Option(value = "-h Print usage information", aliases = { "-help" })
	public boolean help = false;

	@Option(value = "-q Reduce printing during execution", aliases = { "-quiet" })
	public boolean logLvlQuiet = false;

	/**
	 * Be verbose, print extra detailed information. Sets the log level to FINE.
	 */
	@Option(value = "-v Print detailed information during execution ", aliases = { "-verbose" })
	public boolean logLvlVerbose = false;

	@Option(value = "-m Compile a Modular PlusCal spec to vanilla PlusCal", aliases = { "-mpcal" })
	public boolean mpcalCompile = false;

	@Option(value = "-c path to the configuration file, if any")
	public String configFilePath;

	public String inputFilePath;

	// fields extracted from the JSON configuration file
	public String buildDir;
	public String buildFile;
	public PGoNetOptions net;
	public PGoConstantDefs constants;

	private Options plumeOptions;
	private String[] remainingArgs;

	public void printHelp() {
		plumeOptions.print_usage();
	}

	public PGoOptions(String[] args) {
		plumeOptions = new Options("pgo [options] spec", this);
		remainingArgs = plumeOptions.parse_or_usage(args);
	}

	public void parse() throws PGoOptionException {
		if (version) {
			System.out.println("PGo version " + VERSION);
			System.exit(0);
		}

		if (help || remainingArgs.length != 1) {
			printHelp();
			System.exit(0);
		}

		inputFilePath = remainingArgs[0];

		if (!mpcalCompile) {
			// a configuration file is always required unless we are compiling from
			// Modular PlusCal to vanilla PlusCal.
			if (configFilePath == null || configFilePath.isEmpty()) {
				throw new PGoOptionException("Configuration file is required");
			}

			String s;

			try {
				byte[] jsonBytes = Files.readAllBytes(Paths.get(configFilePath));
				s = new String(jsonBytes);
			} catch (IOException ex) {
				throw new PGoOptionException("Error reading configuration file: " + ex.getMessage());
			}

			JSONObject config;

			try {
				config = new JSONObject(s);
			} catch (JSONException e) {
				throw new PGoOptionException(configFilePath + ": parsing error: " + e.getMessage());
			}

			buildDir = config.getJSONObject("build").getString("output_dir");
			buildFile = config.getJSONObject("build").getString("dest_file");
			net = new PGoNetOptions(config);
			constants = new PGoConstantDefs(config, configFilePath);
		}
	}
}
