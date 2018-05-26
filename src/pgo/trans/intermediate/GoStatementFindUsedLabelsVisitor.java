package pgo.trans.intermediate;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import pgo.model.golang.Assignment;
import pgo.model.golang.Block;
import pgo.model.golang.Comment;
import pgo.model.golang.ExpressionStatement;
import pgo.model.golang.For;
import pgo.model.golang.GoCall;
import pgo.model.golang.GoTo;
import pgo.model.golang.If;
import pgo.model.golang.IncDec;
import pgo.model.golang.Label;
import pgo.model.golang.Return;
import pgo.model.golang.Select;
import pgo.model.golang.SelectCase;
import pgo.model.golang.Statement;
import pgo.model.golang.StatementVisitor;
import pgo.model.golang.Switch;
import pgo.model.golang.SwitchCase;

public class GoStatementFindUsedLabelsVisitor extends StatementVisitor<Set<String>, RuntimeException> {

	@Override
	public Set<String> visit(Comment comment) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<String> visit(Assignment assignment) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<String> visit(Return return1) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<String> visit(Block block) throws RuntimeException {
		Set<String> result = new HashSet<>();
		for(Statement stmt : block.getStatements()) {
			result.addAll(stmt.accept(this));
		}
		return result;
	}

	@Override
	public Set<String> visit(For for1) throws RuntimeException {
		return for1.getBody().accept(this);
	}

	@Override
	public Set<String> visit(If if1) throws RuntimeException {
		Set<String> result = new HashSet<>();
		result.addAll(if1.getThen().accept(this));
		result.addAll(if1.getElse().accept(this));
		return result;
	}

	@Override
	public Set<String> visit(Switch switch1) throws RuntimeException {
		Set<String> result = new HashSet<>();
		for(SwitchCase c : switch1.getCases()) {
			for(Statement stmt : c.getBlock()) {
				result.addAll(stmt.accept(this));
			}
		}
		if(switch1.getDefaultBlock() != null) {
			for(Statement stmt : switch1.getDefaultBlock()) {
				result.addAll(stmt.accept(this));
			}
		}
		return result;
	}

	@Override
	public Set<String> visit(Label label) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<String> visit(GoCall goCall) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<String> visit(Select select) throws RuntimeException {
		Set<String> result = new HashSet<>();
		for(SelectCase c : select.getCases()) {
			for(Statement stmt : c.getBlock()) {
				result.addAll(stmt.accept(this));
			}
		}
		return result;
	}

	@Override
	public Set<String> visit(GoTo goTo) throws RuntimeException {
		return Collections.singleton(goTo.getTo().getName());
	}

	@Override
	public Set<String> visit(IncDec incDec) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<String> visit(ExpressionStatement expressionStatement) throws RuntimeException {
		return Collections.emptySet();
	}

}
