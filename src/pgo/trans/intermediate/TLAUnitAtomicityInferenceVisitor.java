package pgo.trans.intermediate;

import pgo.model.tla.*;

public class TLAUnitAtomicityInferenceVisitor extends PGoTLAUnitVisitor<Void, RuntimeException> {
	protected TLAExpressionAtomicityInferenceVisitor visitor;

	public TLAUnitAtomicityInferenceVisitor(TLAExpressionAtomicityInferenceVisitor visitor) {
		this.visitor = visitor;
	}

	@Override
	public Void visit(PGoTLAInstance pGoTLAInstance) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public Void visit(PGoTLAFunctionDefinition pGoTLAFunctionDefinition) throws RuntimeException {
		pGoTLAFunctionDefinition.getFunction().accept(visitor);
		return null;
	}

	@Override
	public Void visit(PGoTLAOperatorDefinition pGoTLAOperator) throws RuntimeException {
		pGoTLAOperator.getBody().accept(visitor);
		return null;
	}

	@Override
	public Void visit(PGoTLATheorem pGoTLATheorem) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public Void visit(PGoTLAModule pGoTLAModule) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public Void visit(PGoTLAVariableDeclaration pGoTLAVariableDeclaration) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public Void visit(PGoTLAConstantDeclaration pGoTLAConstantDeclaration) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public Void visit(PGoTLAModuleDefinition pGoTLAModuleDefinition) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public Void visit(PGoTLAAssumption pGoTLAAssumption) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}
}
