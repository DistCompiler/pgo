package pgo.parser;

import java.util.List;

public class RejectParseAction extends ParseAction {

	private List<ParseAction> toReject;

	public RejectParseAction(List<ParseAction> toReject) {
		this.toReject = toReject;
	}

	public List<ParseAction> getToReject() { return toReject; }

	@Override
	public boolean isDecidable() {
		return true;
	}

	@Override
	public boolean accept(ParseActionExecutor exec) {
		return exec.visit(this);
	}
}
