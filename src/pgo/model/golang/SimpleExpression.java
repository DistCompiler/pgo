package pgo.model.golang;

import java.util.List;
import java.util.Vector;

/**
 * A simple expression: like an assignment
 * 
 */
public class SimpleExpression extends Expression {

	// the tokens in this expression
	private List<Expression> exps;

	public SimpleExpression(List<Expression> exps) {
		this.exps = exps;
	}

	public List<Expression> getExpressions() {
		return this.exps;
	}

	public void setExpressions(List<Expression> exps) {
		this.exps = exps;
	}

	@Override
	public List<String> toGo() {
		Vector<String> eStr = new Vector<>();
		for (int i = 0; i < exps.size(); i++) {
			List<String> e = exps.get(i).toGo();
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