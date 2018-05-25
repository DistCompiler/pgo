package pgo.model.golang;

import java.util.List;

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

}
