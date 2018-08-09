package pgo.model.tla;

public abstract class TLAUnitVisitor<T, E extends Throwable> {
	public abstract T visit(TLAInstance pGoTLAInstance) throws E;
	public abstract T visit(TLAFunctionDefinition pGoTLAFunctionDefinition) throws E;
	public abstract T visit(TLAOperatorDefinition pGoTLAOperator) throws E;
	public abstract T visit(TLATheorem pGoTLATheorem) throws E;
	public abstract T visit(TLAModule pGoTLAModule) throws E;
	public abstract T visit(TLAVariableDeclaration pGoTLAVariableDeclaration) throws E;
	public abstract T visit(TLAConstantDeclaration TLAConstantDeclaration) throws E;
	public abstract T visit(TLAModuleDefinition pGoTLAModuleDefinition) throws E;
	public abstract T visit(TLAAssumption TLAAssumption) throws E;
};
