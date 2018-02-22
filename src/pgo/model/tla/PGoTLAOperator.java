package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

public class PGoTLAOperator {
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
		return name+"("+String.join(", ", args.stream().map(arg -> arg.toString()).collect(Collectors.toList()))+") == "+body;
	}
}
