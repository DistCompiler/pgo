package pgo.model.type;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;

public class NoMatchingFieldIssue extends Issue {
	private final RecordType record;
	private final String fieldName;

	public NoMatchingFieldIssue(RecordType record, String fieldName) {
		this.record = record;
		this.fieldName = fieldName;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public RecordType getRecord() {
		return record;
	}

	public String getFieldName() {
		return fieldName;
	}

}
