package pgo.trans.intermediate;

import pgo.model.golang.*;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

public class GoStatementFindUsedLabelsVisitor extends GoStatementVisitor<Set<String>, RuntimeException> {

	@Override
	public Set<String> visit(GoComment comment) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<String> visit(GoAssignmentStatement assignment) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<String> visit(GoReturn goReturn) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<String> visit(GoBlock block) throws RuntimeException {
		Set<String> result = new HashSet<>();
		for(GoStatement stmt : block.getStatements()) {
			result.addAll(stmt.accept(this));
		}
		return result;
	}

	@Override
	public Set<String> visit(GoFor goFor) throws RuntimeException {
		return goFor.getBody().accept(this);
	}

	@Override
	public Set<String> visit(GoForRange forRange) throws RuntimeException {
		return forRange.getBody().accept(this);
	}

	@Override
	public Set<String> visit(GoIf goIf) throws RuntimeException {
		Set<String> result = new HashSet<>();
		result.addAll(goIf.getThen().accept(this));
		if (goIf.getElse() != null) {
			result.addAll(goIf.getElse().accept(this));
		}
		return result;
	}

	@Override
	public Set<String> visit(GoSwitch goSwitch) throws RuntimeException {
		Set<String> result = new HashSet<>();
		for(GoSwitchCase c : goSwitch.getCases()) {
			for(GoStatement stmt : c.getBlock()) {
				result.addAll(stmt.accept(this));
			}
		}
		if(goSwitch.getDefaultBlock() != null) {
			for(GoStatement stmt : goSwitch.getDefaultBlock()) {
				result.addAll(stmt.accept(this));
			}
		}
		return result;
	}

	@Override
	public Set<String> visit(GoLabel label) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<String> visit(GoSelect select) throws RuntimeException {
		Set<String> result = new HashSet<>();
		for(GoSelectCase c : select.getCases()) {
			for(GoStatement stmt : c.getBlock()) {
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
	public Set<String> visit(GoIncDec incDec) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<String> visit(GoExpressionStatement expressionStatement) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<String> visit(GoBreak break1) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<String> visit(GoContinue continue1) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<String> visit(GoDefer defer) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<String> visit(GoRoutineStatement go) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<String> visit(GoVariableDeclarationStatement variableDeclarationStatement) throws RuntimeException {
		return Collections.emptySet();
	}

}
