package pgo.parser;

public final class Variable<Type> {
	private final String name;

	public Variable(String name) { this.name = name; }

	@Override
	public String toString() { return "Var("+name+", "+hashCode()+")"; }
}
