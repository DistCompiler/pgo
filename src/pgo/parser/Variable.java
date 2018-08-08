package pgo.parser;

import pgo.util.SourceLocatable;

public final class Variable<Type extends SourceLocatable> {
	private final String name;

	public Variable(String name) { this.name = name; }

	@Override
	public String toString() { return "Var("+name+", "+hashCode()+")"; }
}
