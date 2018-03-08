package pgo.model.tla;

public class PGoTLAIdentifier extends PGoTLAIdentifierOrTuple {
	
	String id;
	int line;
	
	public PGoTLAIdentifier(String id, int line) {
		this.id = id;
		this.line = line;
	}
	
	public String getId() {
		return id;
	}
	
	@Override
	public PGoTLAExpression toExpression() {
		return new PGoTLAVariable(id, line);
	}

	@Override
	public <Result> Result walk(PGoTLAIdentifierOrTupleVisitor<Result> v) {
		return v.visit(this);
	}

}
