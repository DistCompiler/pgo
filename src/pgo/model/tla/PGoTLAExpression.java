package pgo.model.tla;

import pgo.util.SourceLocation;

/**
 * Base TLA Expression representation
 *
 */
public abstract class PGoTLAExpression extends PGoTLANode {

	public PGoTLAExpression(SourceLocation location) {
		super(location);
	}
	
	public abstract <T> T accept(Visitor<T> v);
	
	public abstract class Visitor<T>{
		public abstract T visit(PGoTLAFunctionCall pGoTLAFunctionCall);
		public abstract T visit(PGoTLABinOp pGoTLABinOp);
		public abstract T visit(PGoTLABool pGoTLABool);
		public abstract T visit(PGoTLACase pGoTLACase);
		public abstract T visit(PGoTLAExistential pGoTLAExistential);
		public abstract T visit(PGoTLAFunction pGoTLAFunction);
		public abstract T visit(PGoTLAFunctionSet pGoTLAFunctionSet);
		public abstract T visit(PGoTLAFunctionSubstitution pGoTLAFunctionSubstitution);
		public abstract T visit(PGoTLAIf pGoTLAIf);
		public abstract T visit(PGoTLALet pGoTLALet);
		public abstract T visit(PGoTLAGeneralIdentifier pGoTLAVariable);
		public abstract T visit(PGoTLATuple pGoTLATuple);
		public abstract T visit(PGoTLAMaybeAction pGoTLAMaybeAction);
		public abstract T visit(PGoTLANumber pGoTLANumber);
		public abstract T visit(PGoTLAOperatorCall pGoTLAOperatorCall);
		public abstract T visit(PGoTLAQuantifiedExistential pGoTLAQuantifiedExistential);
		public abstract T visit(PGoTLAQuantifiedUniversal pGoTLAQuantifiedUniversal);
		public abstract T visit(PGoTLARecordConstructor pGoTLARecordConstructor);
		public abstract T visit(PGoTLARecordSet pGoTLARecordSet);
		public abstract T visit(PGoTLARequiredAction pGoTLARequiredAction);
		public abstract T visit(PGoTLASetConstructor pGoTLASetConstructor);
		public abstract T visit(PGoTLASetComprehension pGoTLASetComprehension);
		public abstract T visit(PGoTLASetRefinement pGoTLASetRefinement);
		public abstract T visit(PGoTLAString pGoTLAString);
		public abstract T visit(PGoTLAUnary pGoTLAUnary);
		public abstract T visit(PGoTLAUniversal pGoTLAUniversal);
	}

}
