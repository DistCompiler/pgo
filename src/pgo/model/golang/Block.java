package pgo.model.golang;

import java.util.List;
import java.util.Objects;

public class Block extends Statement {
	
	private List<Statement> statements;
	
	public Block(List<Statement> statements) {
		this.statements = statements;
	}
	
	public List<Statement> getStatements(){
		return statements;
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		Block block = (Block) o;
		return Objects.equals(statements, block.statements);
	}

	@Override
	public int hashCode() {

		return Objects.hash(statements);
	}
}
