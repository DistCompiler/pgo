package pgo.trans.passes.scope;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.scope.UID;
import pgo.trans.intermediate.QualifiedName;

public class ScopeConflictIssue extends Issue {
	QualifiedName name;
	UID first;
	UID second;
	
	public ScopeConflictIssue(QualifiedName name, UID first, UID second) {
		super();
		this.name = name;
		this.first = first;
		this.second = second;
	}
	
	public ScopeConflictIssue(String name, UID first, UID second) {
		this.name = new QualifiedName(name);
		this.first = first;
		this.second = second;
	}
	
	public QualifiedName getName() {
		return name;
	}

	public UID getFirst() {
		return first;
	}

	public UID getSecond() {
		return second;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
