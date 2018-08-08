package pgo.parser;

import java.util.regex.Pattern;

public final class PatternParseAction extends ParseAction {

	private Pattern toMatch;
	private int resultLocation;

	public PatternParseAction(Pattern toMatch, int resultLocation){
		this.toMatch = toMatch;
		this.resultLocation = resultLocation;
	}

	@Override
	public String toString(){
		return "MATCH "+toMatch;
	}

	public Pattern getToMatch() { return toMatch; }
	public int getResultLocation() { return resultLocation; }

	@Override
	public boolean isDecidable() {
		return true;
	}

	@Override
	public boolean accept(ParseActionExecutor exec) {
		return exec.visit(this);
	}
}
