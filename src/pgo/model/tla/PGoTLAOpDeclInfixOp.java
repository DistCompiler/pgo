package pgo.model.tla;

/**
 * 
 * A TLA operator definition can look like this:
 * 
 * fn(_ + _) = ...
 * 
 */
public class PGoTLAOpDeclInfixOp extends PGoTLAOpDecl {
	private String op;
	public PGoTLAOpDeclInfixOp(String op){
		this.op = op;
	}
	@Override
	public String toString() {
		return "_"+op+"_";
	}
}
