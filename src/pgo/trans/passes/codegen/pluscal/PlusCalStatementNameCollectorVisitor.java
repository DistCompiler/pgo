package pgo.trans.passes.codegen.pluscal;

import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;

import java.util.Set;

public class PlusCalStatementNameCollectorVisitor extends PlusCalStatementVisitor<Void, RuntimeException> {
	private Set<String> names;

	PlusCalStatementNameCollectorVisitor(Set<String> names) {
		this.names = names;
	}

	@Override
	public Void visit(PlusCalLabeledStatements plusCalLabeledStatements) throws RuntimeException {
		plusCalLabeledStatements.getStatements().forEach(s -> s.accept(this));
		return null;
	}

	@Override
	public Void visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		plusCalWhile.getBody().forEach(s -> s.accept(this));
		return null;
	}

	@Override
	public Void visit(PlusCalIf plusCalIf) throws RuntimeException {
		plusCalIf.getYes().forEach(s -> s.accept(this));
		plusCalIf.getNo().forEach(s -> s.accept(this));
		return null;
	}

	@Override
	public Void visit(PlusCalEither plusCalEither) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PlusCalSkip plusCalSkip) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PlusCalCall plusCalCall) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PlusCalMacroCall macroCall) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PlusCalWith plusCalWith) throws RuntimeException {
		plusCalWith.getVariables().forEach(v -> names.add(v.getName().getValue()));
		plusCalWith.getBody().forEach(s -> s.accept(this));
		return null;
	}

	@Override
	public Void visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		// nothing to do
		return null;
	}
}
