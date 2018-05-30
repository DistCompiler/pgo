package pgo.trans.intermediate;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import pgo.model.golang.*;

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
	public Set<String> visit(ForRange forRange) throws RuntimeException {
		return forRange.getBody().accept(this);
	}

	@Override
	public Set<String> visit(If if1) throws RuntimeException {
		Set<String> result = new HashSet<>();
		result.addAll(if1.getThen().accept(this));
		if (if1.getElse() != null) {
			result.addAll(if1.getElse().accept(this));
		}
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
