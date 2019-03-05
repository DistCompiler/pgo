package pgo.trans.passes.validation;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.formatters.IndentingWriter;
import pgo.formatters.IssueFormattingVisitor;
import pgo.model.mpcal.ModularPlusCalInstance;
import pgo.model.mpcal.ModularPlusCalMapping;
import pgo.model.pcal.PlusCalStatement;

import java.io.IOException;
import java.io.StringWriter;

public class InconsistentInstantiationIssue extends Issue {
    private final ModularPlusCalInstance instance;
    private final ModularPlusCalInstance conflict;

    public InconsistentInstantiationIssue(ModularPlusCalInstance statement, ModularPlusCalInstance conflict) {
        this.instance = statement;
        this.conflict = conflict;
    }

    public ModularPlusCalInstance getInstance() {
        return this.instance;
    }

    public ModularPlusCalInstance getConflict() {
        return this.conflict;
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

        InconsistentInstantiationIssue other = (InconsistentInstantiationIssue) obj;

        return this.getInstance().equals(other.getInstance()) &&
                this.getConflict().equals(other.getConflict());
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