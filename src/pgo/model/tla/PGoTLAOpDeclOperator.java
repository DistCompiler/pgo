package pgo.model.tla;

import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * 
 * TLA operator definitions can look like this:
 * 
 * op(op2(_, _, _)) == ...
 *
 */
public class PGoTLAOpDeclOperator extends PGoTLAOpDecl {
	private String name;
	private int argCount;
	public PGoTLAOpDeclOperator(String name, int argCount) {
		this.name = name;
		this.argCount = argCount;
	}
	
	@Override
	public String toString() {
		return name + "(" + String.join(", ", IntStream.range(0, argCount)
			.boxed()
			.map(x -> "_")
			.collect(Collectors.toList())) + ")";
	}
}
