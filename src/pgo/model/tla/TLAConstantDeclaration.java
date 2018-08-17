package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class TLAConstantDeclaration extends TLAUnit {
	
	private List<TLAOpDecl> constants;

	public TLAConstantDeclaration(SourceLocation location, List<TLAOpDecl> constants) {
		super(location);
		this.constants = constants;
	}
	
	@Override
	public TLAConstantDeclaration copy() {
		return new TLAConstantDeclaration(getLocation(), constants.stream().map(TLAOpDecl::copy).collect(Collectors.toList()));
	}

	public List<TLAOpDecl> getConstants() {
		return constants;
	}

	@Override
	public <T, E extends Throwable> T accept(TLAUnitVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((constants == null) ? 0 : constants.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		TLAConstantDeclaration other = (TLAConstantDeclaration) obj;
		if (constants == null) {
			return other.constants == null;
		} else return constants.equals(other.constants);
	}

}
