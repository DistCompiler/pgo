package pgo.model.golang;

import java.util.Objects;

public class VariableDeclarationStatement extends Statement {
	private VariableDeclaration variableDeclaration;

	public VariableDeclarationStatement(VariableDeclaration variableDeclaration) {
		this.variableDeclaration = variableDeclaration;
	}

	public VariableDeclaration getVariableDeclaration() {
		return variableDeclaration;
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object other) {
		if (this == other) {
			return true;
		}
		if (other == null || getClass() != other.getClass()) {
			return false;
		}
		VariableDeclarationStatement that = (VariableDeclarationStatement) other;
		return Objects.equals(variableDeclaration, that.variableDeclaration);
	}

	@Override
	public int hashCode() {
		return Objects.hashCode(variableDeclaration);
	}
}
