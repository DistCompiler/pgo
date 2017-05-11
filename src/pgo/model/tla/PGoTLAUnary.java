package pgo.model.tla;

/**
 * Represents a TLA unary operator: negation, element union, or powerset.
 * 
 * @author Brandon Zhang
 */
public class PGoTLAUnary extends PGoTLA {
	private String token;
	// The expression the operator operates on
	private PGoTLA arg;
	
	public PGoTLAUnary(String tok, PGoTLA arg, int line) {
		super(line);
		switch (tok) {
		case "~":
		case "\\lnot":
		case "\\neg":
			this.token = "!";
			break;
		default:
			this.token = tok;
			break;
		}
		this.arg = arg;
	}
	
	public String getToken() {
		return token;
	}

	public PGoTLA getArg() {
		return arg;
	}
	
	public String toString() {
		return "PGoTLAUnary (" + this.getLine() + "): " + token + " " + arg.toString();
	}
}
