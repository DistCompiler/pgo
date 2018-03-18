package pgo.model.tla;

/**
 * 
 * TLA operator definitions can look like this:
 * 
 * op(_^*) == ...
 *
 */
public class PGoTLAOpDeclPostfixOp extends PGoTLAOpDecl {
	private String op;
	public PGoTLAOpDeclPostfixOp(String op) {
		this.op = op;
	}
	@Override
	public String toString() {
		return op+"_";
	}
}
