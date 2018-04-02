package pgo.model.tla;

public abstract class PGoTLASubstitutionKeyVisitor<T> {

	public abstract T visit(PGoTLASubstitutionKeyName pGoTLASubstitutionKeyName);

	public abstract T visit(PGoTLASubstitutionKeyIndices pGoTLASubstitutionKeyIndices);

}
