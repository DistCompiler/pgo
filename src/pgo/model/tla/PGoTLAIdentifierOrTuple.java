package pgo.model.tla;

/**
 * 
 * Some parts of the grammar can either result in a single identifier or 
 * a tuple of identifiers. This allows parts of the parser to return
 * the sum type-like result they expect.
 * 
 * a
 * or
 * << a, b, c >>
 *
 */
public abstract class PGoTLAIdentifierOrTuple extends PGoTLANode {
	
	public abstract <Result> Result walk(PGoTLAIdentifierOrTupleVisitor<Result> v);

	public abstract PGoTLAExpression toExpression();
	
	@Override
	public abstract int hashCode();
	
	@Override
	public abstract boolean equals(Object other);
}
