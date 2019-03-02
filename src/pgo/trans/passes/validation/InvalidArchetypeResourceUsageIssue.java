package pgo.trans.passes.validation;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.formatters.IndentingWriter;
import pgo.formatters.IssueFormattingVisitor;
import pgo.model.pcal.PlusCalStatement;
import pgo.util.SourceLocation;

import java.io.IOException;
import java.io.StringWriter;

public class InvalidArchetypeResourceUsageIssue extends Issue {

    private PlusCalStatement statement;
    private String name;
    private boolean isFunction;

    public InvalidArchetypeResourceUsageIssue(PlusCalStatement statement, String name, boolean isFunction) {
        this.statement = statement;
        this.name = name;
        this.isFunction = isFunction;
    }

    public PlusCalStatement getStatement() {
        return this.statement;
    }

    public String getName() {
        return name;
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
                this.getName().equals(other.getName()) &&
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