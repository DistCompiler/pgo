package pgo.parser;

public class EOFParseAction extends ParseAction {
	@Override
	public boolean isDecidable() {
		return true;
	}

	@Override
	public boolean accept(ParseActionExecutor exec) {
		return exec.visit(this);
	}
}
