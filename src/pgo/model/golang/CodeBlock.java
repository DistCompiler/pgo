package pgo.model.golang;

import java.util.List;
import java.util.Vector;

/**
 * Represents a code block { ... }. This is used with compilation of "with", for
 * example, to control variable scoping.
 *
 */
public class CodeBlock extends Statement {
	// the contained statements
	private Vector<Statement> stmts;
	
	public CodeBlock(Vector<Statement> inside) {
		stmts = inside;
	}
	
	public List<Statement> getInside() {
		return stmts;
	}

	@Override
	public List<String> toGo() {
		Vector<String> ret = new Vector<>();
		ret.add("{");
		addIndentedAST(ret, stmts);
		ret.add("}");
		return ret;
	}

}
