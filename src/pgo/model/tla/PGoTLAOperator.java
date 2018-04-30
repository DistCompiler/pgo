package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

/**
 * 
 * TLA AST Node representing a defined operator.
 * 
 * op(...) == ...
 *
 */
public class PGoTLAOperator extends PGoTLANode {
	private String name;
	private List<PGoTLAOpDecl> args;
	private PGoTLAExpression body;
	public PGoTLAOperator(String name, List<PGoTLAOpDecl> args, PGoTLAExpression body) {
		this.name = name;
		this.args = args;
		this.body = body;
	}
	@Override
	public String toString() {
		return "PGoTLAOperator [name=" + name + ", args=" + args + ", body=" + body + "]";
	}
}
