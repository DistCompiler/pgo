package pgo.model.golang;

import java.util.List;
import java.util.Vector;

/**
 * A select statement in go
 */
public class Select extends Statement {

	// the cases
	private List<Expression> cases;

	// the body per case
	private List<List<Statement>> body;

	public Select(List<Expression> cases, List<List<Statement>> body) {
		assert (cases.size() == body.size());
		this.cases = cases;
		this.body = body;
	}

	public List<Expression> getCases() {
		return cases;
	}

	public void setCases(List<Expression> cases) {
		this.cases = cases;
	}

	public List<List<Statement>> getBodies() {
		return this.body;
	}

	public void setBodies(List<List<Statement>> b) {
		this.body = b;
	}

	@Override
	public List<String> toGo() {
		Vector<String> ret = new Vector<>();
		ret.add("select {");
		for (int i = 0; i < cases.size(); ++i) {
			List<String> caseStr = cases.get(i).toGo();
			ret.add("case " + caseStr.get(0));
			caseStr = caseStr.subList(1, caseStr.size());
			addStringsAndIndent(ret, caseStr);
			ret.add(ret.remove(ret.size() - 1) + ":");
			addIndentedAST(ret, body.get(i));
		}
		ret.add("}");
		return ret;
	}
}
