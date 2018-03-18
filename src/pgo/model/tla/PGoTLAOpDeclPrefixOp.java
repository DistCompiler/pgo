package pgo.model.tla;

/**
 * 
 * TLA operator definitions can look like this:
 * 
 * op(-_) == ...
 *
 */
public class PGoTLAOpDeclPrefixOp extends PGoTLAOpDecl {
	private String op;
	public PGoTLAOpDeclPrefixOp(String op) {
		this.op = op;
	}
	@Override
	public String toString() {
		return op+"_";
	}
}
