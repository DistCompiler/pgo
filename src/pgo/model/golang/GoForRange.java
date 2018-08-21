package pgo.model.golang;

import java.util.List;
import java.util.Objects;

/**
 * Represents a for _ := range _ loop in GoRoutineStatement
 */
public class GoForRange extends GoStatement {
	private List<GoExpression> lhs;
	private boolean defines;
	private GoExpression rangeExpr;

	private GoBlock body;

	public GoForRange(List<GoExpression> lhs, boolean defines, GoExpression rangeExpr, GoBlock body) {
		this.lhs = lhs;
		this.defines = defines;
		this.rangeExpr = rangeExpr;
		this.body = body;
	}

	public List<GoExpression> getLhs() {
		return lhs;
	}

	public boolean isDefinition() {
		return defines;
	}

	public GoExpression getRangeExpr() {
		return rangeExpr;
	}

	public GoBlock getBody() {
		return body;
	}

	@Override
	public <T, E extends Throwable> T accept(GoStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoForRange forRange = (GoForRange) o;
		return defines == forRange.defines &&
				Objects.equals(lhs, forRange.lhs) &&
				Objects.equals(rangeExpr, forRange.rangeExpr) &&
				Objects.equals(body, forRange.body);
	}

	@Override
	public int hashCode() {

		return Objects.hash(lhs, defines, rangeExpr, body);
	}
}
