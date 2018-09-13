package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.pcal.PlusCalStatement;

public class InvalidModularPlusCalIssue extends Issue {

    public enum InvalidReason {
        MISSING_LABEL,
    }

    private InvalidReason reason;
    private PlusCalStatement statement;

    public InvalidModularPlusCalIssue(InvalidReason reason, PlusCalStatement statement) {
        this.reason = reason;
        this.statement = statement;
    }

    public PlusCalStatement getStatement() {
        return this.statement;
    }

    public InvalidReason getReason() {
        return this.reason;
    }

    public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
        return v.visit(this);
    }
}
