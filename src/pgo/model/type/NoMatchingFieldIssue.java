package pgo.model.type;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;

public class NoMatchingFieldIssue extends Issue {
	private final PGoTypeConcreteRecord record;
	private final String fieldName;

	public NoMatchingFieldIssue(PGoTypeConcreteRecord record, String fieldName) {
		this.record = record;
		this.fieldName = fieldName;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public PGoTypeConcreteRecord getRecord() {
		return record;
	}

	public String getFieldName() {
		return fieldName;
	}

}
