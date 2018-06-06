package pgo;

import java.util.HashMap;
import java.util.logging.Level;
import java.util.logging.Logger;

import pgo.parser.PGoParseException;
import pgo.parser.PcalParser;
import pgo.parser.PcalParser.ParsedPcal;

/**
 * Abstract class for testing data of real pluscal algorithms for any stage.
 *
 */
public abstract class PGoPluscalTesterBase {
	private static HashMap<String, ParsedPcal> parsedPcal = new HashMap<String, ParsedPcal>();

	// Gets the parsed version of this pluscal algorithm
	public ParsedPcal getParsedPcal() throws PGoParseException {
		ParsedPcal r = parsedPcal.get(getAlg());
		if (r != null) {
			return r;
		}
		Logger.getLogger("PGoTrans AST Stage").setLevel(Level.INFO);
		r = new PcalParser(getPcalPath()).parse();
		parsedPcal.put(getAlg(), r);
		return r;
	}

	public String getPcalPath() {
		return "./test/pluscal/" + getAlg() + ".tla";
	}

	public void clearPcal() {
		parsedPcal.remove(getAlg());
	}

	// The name of the algorithm
	protected abstract String getAlg();
}
