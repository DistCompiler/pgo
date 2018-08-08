package pgo.parser;

public final class StringParseAction extends ParseAction {

	private String toMatch;
	private int resultLocation;

	public StringParseAction(String toMatch, int resultLocation){
		this.toMatch = toMatch;
		this.resultLocation = resultLocation;
	}

	@Override
	public String toString(){
		return "STR \""+toMatch+"\"";
	}

	public String getToMatch() { return toMatch; }
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
