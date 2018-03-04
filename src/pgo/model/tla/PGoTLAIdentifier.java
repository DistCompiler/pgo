package pgo.model.tla;

public class PGoTLAIdentifier extends PGoTLAIdentifierOrTuple {
	
	String id;
	
	public PGoTLAIdentifier(String id) {
		this.id = id;
	}
	
	public String getId() {
		return id;
	}

	@Override
	public <Result> Result walk(PGoTLAIdentifierOrTupleVisitor<Result> v) {
		return v.visit(this);
	}

}
