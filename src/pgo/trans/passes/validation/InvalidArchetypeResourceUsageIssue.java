package pgo.trans.passes.validation;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.formatters.IndentingWriter;
import pgo.formatters.IssueFormattingVisitor;
import pgo.model.pcal.PlusCalStatement;
import pgo.scope.UID;

import java.io.IOException;
import java.io.StringWriter;

public class InvalidArchetypeResourceUsageIssue extends Issue {
    private final PlusCalStatement statement;
    private final UID varUID;
    private final boolean isFunction;

    public InvalidArchetypeResourceUsageIssue(PlusCalStatement statement, UID varUID, boolean isFunction) {
        this.statement = statement;
        this.varUID = varUID;
        this.isFunction = isFunction;
    }

    public PlusCalStatement getStatement() {
        return this.statement;
    }

    public UID getVarUID() {
        return varUID;
    }

    public boolean isFunction() {
        return isFunction;
    }

    public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
        return v.visit(this);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;

        if (obj == null)
            return false;

        if (this.getClass() != obj.getClass())
            return false;

        InvalidArchetypeResourceUsageIssue other = (InvalidArchetypeResourceUsageIssue) obj;

        return this.getStatement().equals(other.getStatement()) &&
                this.getVarUID().equals(other.getVarUID()) &&
                this.isFunction == other.isFunction;
    }

    @Override
    public String toString() {
        StringWriter w = new StringWriter();
        IndentingWriter out = new IndentingWriter(w);

        try {
            this.accept(new IssueFormattingVisitor(out));
        } catch (IOException err) {
            throw new RuntimeException("Error formatting issue", err);
        }

        return w.toString();
    }
}