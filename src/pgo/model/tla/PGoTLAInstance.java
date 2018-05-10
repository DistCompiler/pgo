package pgo.model.tla;

import java.util.Map;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST Node:
 * 
 * INSTANCE ModuleName (WITH a <- <expr>, b <- <expr>)?
 *
 */
public class PGoTLAInstance extends PGoTLAUnit {
	PGoTLAIdentifier moduleName;
	Map<PGoTLAOpDecl, PGoTLAExpression> remappings;
	private boolean local;
	
	public PGoTLAInstance(SourceLocation location, PGoTLAIdentifier referenceName, PGoTLAIdentifier moduleName, Map<PGoTLAOpDecl, PGoTLAExpression> remappings, boolean isLocal) {
		super(location);
		this.moduleName = moduleName;
		this.remappings = remappings;
		this.local = isLocal;
	}
	
	public PGoTLAIdentifier getModuleName() {
		return moduleName;
	}
	
	public Map<PGoTLAOpDecl, PGoTLAExpression> getRemappings(){
		return remappings;
	}
	
	public boolean isLocal() {
		return local;
	}
	
	@Override
	public <T> T accept(Visitor<T> v) {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (local ? 1231 : 1237);
		result = prime * result + ((moduleName == null) ? 0 : moduleName.hashCode());
		result = prime * result + ((remappings == null) ? 0 : remappings.hashCode());
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
		PGoTLAInstance other = (PGoTLAInstance) obj;
		if (local != other.local)
			return false;
		if (moduleName == null) {
			if (other.moduleName != null)
				return false;
		} else if (!moduleName.equals(other.moduleName))
			return false;
		if (remappings == null) {
			if (other.remappings != null)
				return false;
		} else if (!remappings.equals(other.remappings))
			return false;
		return true;
	}

}
