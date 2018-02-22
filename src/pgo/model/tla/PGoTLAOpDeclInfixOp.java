package pgo.model.tla;

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
