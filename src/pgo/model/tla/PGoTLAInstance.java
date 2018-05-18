package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST Node:
 * 
 * INSTANCE ModuleName (WITH a <- <expr>, b <- <expr>)?
 *
 */
public class PGoTLAInstance extends PGoTLAUnit {
	private PGoTLAIdentifier moduleName;
	private List<Remapping> remappings;
	private boolean local;
	
	public PGoTLAInstance(SourceLocation location, PGoTLAIdentifier moduleName, List<Remapping> remappings, boolean isLocal) {
		super(location);
		this.moduleName = moduleName;
		this.remappings = remappings;
		this.local = isLocal;
	}
	
	@Override
	public PGoTLAInstance copy() {
		return new PGoTLAInstance(getLocation(), moduleName.copy(), remappings.stream().map(Remapping::copy).collect(Collectors.toList()), local);
	}
	
	public static class Remapping extends PGoTLANode{
		PGoTLAIdentifier from;
		PGoTLAExpression to;
		public Remapping(SourceLocation location, PGoTLAIdentifier from, PGoTLAExpression to) {
			super(location);
			this.from = from;
			this.to = to;
		}
		public PGoTLAIdentifier getFrom() {
			return from;
		}
		public PGoTLAExpression getTo() {
			return to;
		}
		@Override
		public Remapping copy() {
			return new Remapping(getLocation(), from.copy(), to.copy());
		}
		@Override
		public <T, E extends Throwable> T accept(PGoTLANodeVisitor<T, E> v) throws E {
			return v.visit(this);
		}
		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((from == null) ? 0 : from.hashCode());
			result = prime * result + ((to == null) ? 0 : to.hashCode());
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
			Remapping other = (Remapping) obj;
			if (from == null) {
				if (other.from != null)
					return false;
			} else if (!from.equals(other.from))
				return false;
			if (to == null) {
				if (other.to != null)
					return false;
			} else if (!to.equals(other.to))
				return false;
			return true;
		}
	}
	
	public PGoTLAIdentifier getModuleName() {
		return moduleName;
	}
	
	public List<Remapping> getRemappings(){
		return remappings;
	}
	
	public boolean isLocal() {
		return local;
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTLAUnitVisitor<T, E> v) throws E {
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
