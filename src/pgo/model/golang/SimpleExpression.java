package pgo.model.golang;

import java.util.Vector;

/**
 * A simple expression: like an assignment
 * 
 */
public class SimpleExpression extends Expression {

	// the tokens in this expression
	private Vector<Expression> exps;

	public SimpleExpression(Vector<Expression> exps) {
		this.exps = exps;
	}

	public Vector<Expression> getExpressions() {
		return this.exps;
	}

	public void setExpressions(Vector<Expression> exps) {
		this.exps = exps;
	}

	public void merge(SimpleExpression s) {
		exps.addAll(s.exps);
	}

	@Override
	public Vector<String> toGo() {

		Vector<String> eStr = new Vector<String>();

		for (int i = 0; i < exps.size(); i++) {
			Vector<String> e = exps.get(i).toGo();
			for (int j = 0; j < e.size(); j++) {
				if (j > 0) {
					eStr.add(e.get(j));
				} else {
					// param is one line
					if (i == 0) {
						eStr.add(e.get(j));
					} else {
						eStr.add(eStr.remove(eStr.size() - 1) + e.get(j));
					}
				}
			}
		}

		return eStr;
	}

}