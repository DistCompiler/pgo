package pgo.model.tla;

public abstract class PGoTLAIdentifierOrTuple {
	
	public abstract <Result> Result walk(PGoTLAIdentifierOrTupleVisitor<Result> v);

	public abstract PGoTLAExpression toExpression();
}
