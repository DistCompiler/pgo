package pgo.parser;

public class AssignmentParseAction extends ParseAction {

	private int fromLocation;
	private int toLocation;

	public AssignmentParseAction(int fromLocation, int toLocation) {
		this.fromLocation = fromLocation;
		this.toLocation = toLocation;
	}

	public int getFromLocation() { return fromLocation; }
	public int getToLocation() { return toLocation; }

	@Override
	public boolean isDecidable() {
		return false;
	}

	@Override
	public boolean accept(ParseActionExecutor exec) {
		return exec.visit(this);
	}
}
