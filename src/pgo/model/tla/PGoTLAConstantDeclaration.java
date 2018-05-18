package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class PGoTLAConstantDeclaration extends PGoTLAUnit {
	
	private List<PGoTLAOpDecl> constants;

	public PGoTLAConstantDeclaration(SourceLocation location, List<PGoTLAOpDecl> constants) {
		super(location);
		this.constants = constants;
	}
	
	@Override
	public PGoTLAConstantDeclaration copy() {
		return new PGoTLAConstantDeclaration(getLocation(), constants.stream().map(PGoTLAOpDecl::copy).collect(Collectors.toList()));
	}

	public List<PGoTLAOpDecl> getConstants() {
		return constants;
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTLAUnitVisitor<T, E> v) throws E {
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
		PGoTLAConstantDeclaration other = (PGoTLAConstantDeclaration) obj;
		if (constants == null) {
			if (other.constants != null)
				return false;
		} else if (!constants.equals(other.constants))
			return false;
		return true;
	}

}
