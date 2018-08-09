package pgo.model.golang;

import java.util.List;
import java.util.Objects;

public class GoBlock extends GoStatement {
	
	private List<GoStatement> statements;
	
	public GoBlock(List<GoStatement> statements) {
		this.statements = statements;
	}
	
	public List<GoStatement> getStatements(){
		return statements;
	}

	@Override
	public <T, E extends Throwable> T accept(GoStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoBlock block = (GoBlock) o;
		return Objects.equals(statements, block.statements);
	}

	@Override
	public int hashCode() {

		return Objects.hash(statements);
	}
}
