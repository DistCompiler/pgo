package pgo.trans.intermediate;

import pgo.model.golang.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

public class GoStatementRemoveUnusedLabelsVisitor extends GoStatementVisitor<GoStatement, RuntimeException> {

	private Set<String> usedLabels;

	public GoStatementRemoveUnusedLabelsVisitor(Set<String> usedLabels) {
		this.usedLabels = usedLabels;
	}

	private List<GoStatement> filterBlock(List<GoStatement> block){
		List<GoStatement> result = new ArrayList<>();
		for(GoStatement stmt : block) {
			GoStatement next = stmt.accept(this);
			if(next != null) {
				result.add(next);
			}
		}
		return result;
	}

	@Override
	public GoStatement visit(GoComment comment) throws RuntimeException {
		return comment;
	}

	@Override
	public GoStatement visit(GoAssignmentStatement assignment) throws RuntimeException {
		return assignment;
	}

	@Override
	public GoStatement visit(GoReturn goReturn) throws RuntimeException {
		return goReturn;
	}

	@Override
	public GoStatement visit(GoBlock block) throws RuntimeException {
		return new GoBlock(filterBlock(block.getStatements()));
	}

	@Override
	public GoStatement visit(GoFor goFor) throws RuntimeException {
		return new GoFor(goFor.getInit(), goFor.getCondition(), goFor.getIncrement(), (GoBlock) goFor.getBody().accept(this));
	}

	@Override
	public GoStatement visit(GoForRange forRange) throws RuntimeException {
		return new GoForRange(forRange.getLhs(), forRange.isDefinition(), forRange.getRangeExpr(),
				(GoBlock) forRange.getBody().accept(this));
	}

	@Override
	public GoStatement visit(GoIf goIf) throws RuntimeException {
		return new GoIf(
				goIf.getCond(),
				(GoBlock) goIf.getThen().accept(this),
				goIf.getElse() != null ? (GoBlock) goIf.getElse().accept(this) : null);
	}

	@Override
	public GoStatement visit(GoSwitch goSwitch) throws RuntimeException {
		List<GoSwitchCase> cases = new ArrayList<>();
		for(GoSwitchCase c : goSwitch.getCases()) {
			cases.add(new GoSwitchCase(c.getCondition(), filterBlock(c.getBlock())));
		}
		List<GoStatement> defaultBlock = null;
		if(goSwitch.getDefaultBlock() != null) {
			defaultBlock = filterBlock(goSwitch.getDefaultBlock());
		}
		return new GoSwitch(goSwitch.getCondition(), cases, defaultBlock);
	}

	@Override
	public GoStatement visit(GoLabel label) throws RuntimeException {
		if(usedLabels.contains(label.getName())) {
			return label;
		}else {
			return null;
		}
	}

	@Override
	public GoStatement visit(GoSelect select) throws RuntimeException {
		List<GoSelectCase> cases = new ArrayList<>();
		for(GoSelectCase c : select.getCases()) {
			cases.add(new GoSelectCase(c.getCondition(), filterBlock(c.getBlock())));
		}
		return new GoSelect(cases);
	}

	@Override
	public GoStatement visit(GoTo goTo) throws RuntimeException {
		return goTo;
	}

	@Override
	public GoStatement visit(GoIncDec incDec) throws RuntimeException {
		return incDec;
	}

	@Override
	public GoStatement visit(GoExpressionStatement expressionStatement) throws RuntimeException {
		return expressionStatement;
	}

	@Override
	public GoStatement visit(GoBreak break1) throws RuntimeException {
		return break1;
	}

	@Override
	public GoStatement visit(GoContinue continue1) throws RuntimeException {
		return continue1;
	}

	@Override
	public GoStatement visit(GoDefer defer) throws RuntimeException {
		return defer;
	}

	@Override
	public GoStatement visit(GoRoutineStatement go) throws RuntimeException {
		return go;
	}

	@Override
	public GoStatement visit(GoVariableDeclarationStatement variableDeclarationStatement) throws RuntimeException {
		return variableDeclarationStatement;
	}

}
