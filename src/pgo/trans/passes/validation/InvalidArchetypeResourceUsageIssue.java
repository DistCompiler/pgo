package pgo.trans.passes.validation;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.formatters.IndentingWriter;
import pgo.formatters.IssueFormattingVisitor;
import pgo.model.pcal.PlusCalStatement;
import pgo.scope.UID;

import java.io.IOException;
import java.io.StringWriter;
import java.util.Objects;

public final class InvalidArchetypeResourceUsageIssue extends Issue {
    private final PlusCalStatement statement;
    private final boolean isFunction;

    public InvalidArchetypeResourceUsageIssue(PlusCalStatement statement, boolean isFunction) {
        this.statement = statement;
        this.isFunction = isFunction;
    }

    public PlusCalStatement getStatement() {
        return this.statement;
    }

    public boolean isFunction() {
        return isFunction;
    }

    public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
        return v.visit(this);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        InvalidArchetypeResourceUsageIssue that = (InvalidArchetypeResourceUsageIssue) o;
        return isFunction == that.isFunction && Objects.equals(statement, that.statement);
    }

    @Override
    public int hashCode() {
        return Objects.hash(statement, isFunction);
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