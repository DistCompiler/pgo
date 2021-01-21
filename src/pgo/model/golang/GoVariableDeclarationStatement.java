package pgo.model.golang;

import java.util.Objects;

public class GoVariableDeclarationStatement extends GoStatement {
	private final GoVariableDeclaration variableDeclaration;

	public GoVariableDeclarationStatement(GoVariableDeclaration variableDeclaration) {
		this.variableDeclaration = variableDeclaration;
	}

	public GoVariableDeclaration getVariableDeclaration() {
		return variableDeclaration;
	}

	@Override
	public <T, E extends Throwable> T accept(GoStatementVisitor<T, E> v) throws E {
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
		GoVariableDeclarationStatement that = (GoVariableDeclarationStatement) other;
		return Objects.equals(variableDeclaration, that.variableDeclaration);
	}

	@Override
	public int hashCode() {
		return Objects.hashCode(variableDeclaration);
	}
}
