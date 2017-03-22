package pgo;

import java.util.HashMap;
import java.util.logging.Level;
import java.util.logging.Logger;

import pcal.AST;
import pgo.pcalparser.PcalParseException;
import pgo.pcalparser.PcalParser;
import pgo.pcalparser.PcalParser.ParsedPcal;

/**
 * Abstract class for testing data of real pluscal algorithms for any stage.
 *
 */
public abstract class PGoPluscalTesterBase {
	private static HashMap<String, ParsedPcal> parsedPcal = new HashMap<String, ParsedPcal>();

	// Gets the parsed version of this pluscal algorithm
	public AST getAST() throws PcalParseException {
		ParsedPcal r = parsedPcal.get(getAlg());
		if (r != null) {
			return r.getAST();
		}
		Logger.getLogger("PGoTrans AST Stage").setLevel(Level.INFO);
		r = new PcalParser("./test/pluscal/" + getAlg() + ".tla").parse();
		parsedPcal.put(getAlg(), r);
		return r.getAST();
	}

	protected abstract String getAlg();
}
