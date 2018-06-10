package pgo.model.golang;

import java.util.Objects;

public class Selector extends Expression {
	
	Expression lhs;
	String name;
	
	public Selector(Expression lhs, String name) {
		this.lhs = lhs;
		this.name = name;
	}
	
	public Expression getLHS() {
		return lhs;
	}
	
	public String getName() {
		return name;
	}

	@Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		Selector selector = (Selector) o;
		return Objects.equals(lhs, selector.lhs) &&
				Objects.equals(name, selector.name);
	}

	@Override
	public int hashCode() {

		return Objects.hash(lhs, name);
	}
}
