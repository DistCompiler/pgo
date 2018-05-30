package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import pgo.model.golang.*;

public class GoStatementRemoveUnusedLabelsVisitor extends StatementVisitor<Statement, RuntimeException> {

	private Set<String> usedLabels;

	public GoStatementRemoveUnusedLabelsVisitor(Set<String> usedLabels) {
		this.usedLabels = usedLabels;
	}

	private List<Statement> filterBlock(List<Statement> block){
		List<Statement> result = new ArrayList<>();
		for(Statement stmt : block) {
			Statement next = stmt.accept(this);
			if(next != null) {
				result.add(next);
			}
		}
		return result;
	}

	@Override
	public Statement visit(Comment comment) throws RuntimeException {
		return comment;
	}

	@Override
	public Statement visit(Assignment assignment) throws RuntimeException {
		return assignment;
	}

	@Override
	public Statement visit(Return return1) throws RuntimeException {
		return return1;
	}

	@Override
	public Statement visit(Block block) throws RuntimeException {
		return new Block(filterBlock(block.getStatements()));
	}

	@Override
	public Statement visit(For for1) throws RuntimeException {
		return new For(for1.getInit(), for1.getCondition(), for1.getIncrement(), (Block)for1.getBody().accept(this));
	}

	@Override
	public Statement visit(ForRange forRange) throws RuntimeException {
		return new ForRange(forRange.getLhs(), forRange.isDefinition(), forRange.getRangeExpr(),
				(Block) forRange.getBody().accept(this));
	}

	@Override
	public Statement visit(If if1) throws RuntimeException {
		return new If(
				if1.getCond(),
				(Block)if1.getThen().accept(this),
				if1.getElse() != null ? (Block)if1.getElse().accept(this) : null);
	}

	@Override
	public Statement visit(Switch switch1) throws RuntimeException {
		List<SwitchCase> cases = new ArrayList<>();
		for(SwitchCase c : switch1.getCases()) {
			cases.add(new SwitchCase(c.getCondition(), filterBlock(c.getBlock())));
		}
		List<Statement> defaultBlock = null;
		if(switch1.getDefaultBlock() != null) {
			defaultBlock = filterBlock(switch1.getDefaultBlock());
		}
		return new Switch(switch1.getCondition(), cases, defaultBlock);
	}

	@Override
	public Statement visit(Label label) throws RuntimeException {
		if(usedLabels.contains(label.getName())) {
			return label;
		}else {
			return null;
		}
	}

	@Override
	public Statement visit(GoCall goCall) throws RuntimeException {
		return goCall;
	}

	@Override
	public Statement visit(Select select) throws RuntimeException {
		List<SelectCase> cases = new ArrayList<>();
		for(SelectCase c : select.getCases()) {
			cases.add(new SelectCase(c.getCondition(), filterBlock(c.getBlock())));
		}
		return new Select(cases);
	}

	@Override
	public Statement visit(GoTo goTo) throws RuntimeException {
		return goTo;
	}

	@Override
	public Statement visit(IncDec incDec) throws RuntimeException {
		return incDec;
	}

	@Override
	public Statement visit(ExpressionStatement expressionStatement) throws RuntimeException {
		return expressionStatement;
	}

}
