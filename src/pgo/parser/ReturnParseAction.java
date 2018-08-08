package pgo.parser;

public class ReturnParseAction extends ParseAction {

	private int returnSrc;

	public ReturnParseAction(int returnSrc) {
		this.returnSrc = returnSrc;
	}

	public int getReturnSource() { return returnSrc; }

	@Override
	public boolean isDecidable() {
		return false;
	}

	@Override
	public boolean accept(ParseActionExecutor exec) {
		return exec.visit(this);
	}
}
