package pgo.model.tla;

public abstract class PGoTLAUnitVisitor<T, E extends Throwable> {
	public abstract T visit(PGoTLAInstance pGoTLAInstance) throws E;
	public abstract T visit(PGoTLAFunctionDefinition pGoTLAFunctionDefinition) throws E;
	public abstract T visit(PGoTLAOperatorDefinition pGoTLAOperator) throws E;
	public abstract T visit(PGoTLATheorem pGoTLATheorem) throws E;
	public abstract T visit(PGoTLAModule pGoTLAModule) throws E;
	public abstract T visit(PGoTLAVariableDeclaration pGoTLAVariableDeclaration) throws E;
	public abstract T visit(PGoTLAConstantDeclaration pGoTLAConstantDeclaration) throws E;
	public abstract T visit(PGoTLAModuleDefinition pGoTLAModuleDefinition) throws E;
	public abstract T visit(PGoTLAAssumption pGoTLAAssumption) throws E;
};
