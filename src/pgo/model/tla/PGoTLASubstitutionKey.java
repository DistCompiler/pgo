package pgo.model.tla;

public abstract class PGoTLASubstitutionKey {

	public abstract <T> T accept(PGoTLASubstitutionKeyVisitor<T> visitor);
	
	@Override
	public abstract int hashCode();
	
	@Override
	public abstract boolean equals(Object other);
}
