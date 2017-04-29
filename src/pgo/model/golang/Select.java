package pgo.model.golang;

import java.util.Vector;

/**
 * A select statement in go
 *
 *
 */
public class Select extends Statement {

	// the cases
	private Vector<Expression> cases;

	// the body per case
	private Vector<Vector<Statement>> body;

	public Select(Vector<Expression> cases, Vector<Vector<Statement>> body) {
		assert (cases.size() == body.size());
		this.cases = cases;
		this.body = body;
	}

	public Vector<Expression> getCases() {
		return cases;
	}

	public void setCases(Vector<Expression> cases) {
		this.cases = cases;
	}

	public Vector<Vector<Statement>> getBodies() {
		return this.body;
	}

	public void setBodies(Vector<Vector<Statement>> b) {
		this.body = b;
	}

	@Override
	public Vector<String> toGo() {
		Vector<String> ret = new Vector<String>();
		ret.add("select {");
		for (int i = 0; i < cases.size(); ++i) {
			Vector<String> caseStr = cases.get(i).toGo();
			ret.add("case " + caseStr.remove(0));
			addIndented(ret, caseStr);
			ret.add(ret.remove(ret.size() - 1) + ":");
			addIndented(ret, body.get(i));
		}
		ret.add("}");
		return ret;
	}
}
