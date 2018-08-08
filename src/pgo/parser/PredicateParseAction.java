package pgo.parser;

import pgo.util.SourceLocatable;

import java.util.function.Predicate;

public class PredicateParseAction<Arg extends SourceLocatable> extends ParseAction {

	private int argLocation;
	private Predicate<ParseInfo<Arg>> predicate;

	public PredicateParseAction(int argLocation, Predicate<ParseInfo<Arg>> predicate) {
		this.argLocation = argLocation;
		this.predicate = predicate;
	}

	public int getArgLocation() { return argLocation; }
	public Predicate<ParseInfo<Arg>> getPredicate() { return predicate; }

	@Override
	public boolean isDecidable() {
		return true;
	}

	@Override
	public boolean accept(ParseActionExecutor exec) {
		return exec.visit(this);
	}
}
