package pgo.parser;

import java.util.ArrayList;
import java.util.List;

public class FailParseAction extends ParseAction {

	private List<ParseFailure> failures;

	public FailParseAction(ParseFailure failure) {
		this.failures = new ArrayList<>();
		this.failures.add(failure);
	}

	public List<ParseFailure> getFailures() { return failures; }

	@Override
	public String toString() {
		return "FAIL "+failures;
	}

	@Override
	public boolean isDecidable() {
		return true;
	}

	@Override
	public boolean accept(ParseActionExecutor exec) {
		return exec.visit(this);
	}
}
