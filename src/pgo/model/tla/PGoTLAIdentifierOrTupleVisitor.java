package pgo.model.tla;

public abstract class PGoTLAIdentifierOrTupleVisitor<Result> {
	public abstract Result visit(PGoTLAIdentifierTuple tp);
	public abstract Result visit(PGoTLAIdentifier id);
}
