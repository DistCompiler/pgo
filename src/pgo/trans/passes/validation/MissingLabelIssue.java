package pgo.trans.passes.validation;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.formatters.IndentingWriter;
import pgo.formatters.IssueFormattingVisitor;
import pgo.model.pcal.PlusCalStatement;

import java.io.IOException;
import java.io.StringWriter;

public class MissingLabelIssue extends Issue {

    private PlusCalStatement statement;

    public MissingLabelIssue(PlusCalStatement statement) {
        this.statement = statement;
    }

    public PlusCalStatement getStatement() {
        return this.statement;
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

        MissingLabelIssue other = (MissingLabelIssue) obj;

        return this.getStatement().equals(other.getStatement());
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
