package pgo.model.golang;

import java.util.List;

/**
 * Represents a for _ := range _ loop in Go
 */
public class ForRange extends Statement {
	private List<Expression> lhs;
	private boolean defines;
	private Expression rangeExpr;

	private Block body;

	public ForRange(List<Expression> lhs, boolean defines, Expression rangeExpr, Block body) {
		this.lhs = lhs;
		this.defines = defines;
		this.rangeExpr = rangeExpr;
		this.body = body;
	}

	public List<Expression> getLhs() {
		return lhs;
	}

	public boolean isDefinition() {
		return defines;
	}

	public Expression getRangeExpr() {
		return rangeExpr;
	}

	public Block getBody() {
		return body;
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
