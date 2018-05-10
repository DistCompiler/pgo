package pgo.model.tla;

import pgo.util.SourceLocation;

public abstract class PGoTLAUnit extends PGoTLANode {
	
	public PGoTLAUnit(SourceLocation location) {
		super(location);
	}
	
	public abstract <T> T accept(Visitor<T> v);
	
	public abstract class Visitor<T> {
		public abstract T visit(PGoTLAInstance pGoTLAInstance);
		public abstract T visit(PGoTLAFunctionDefinition pGoTLAFunctionDefinition);
		public abstract T visit(PGoTLAOperatorDefinition pGoTLAOperator);
		public abstract T visit(PGoTLATheorem pGoTLATheorem);
		public abstract T visit(PGoTLAModule pGoTLAModule);
		public abstract T visit(PGoTLAVariableDeclaration pGoTLAVariableDeclaration);
		public abstract T visit(PGoTLAConstantDeclaration pGoTLAConstantDeclaration);
		public abstract T visit(PGoTLAModuleDefinition pGoTLAModuleDefinition);
		public abstract T visit(PGoTLAAssumption pGoTLAAssumption);
	};

}
