package pgo.model.tla;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST Node, representing the kinds of things you can find in
 * TLA operator definition parameter lists. The special cases are usually
 * used for higher-order operators.
 *
 */
public class PGoTLAOpDecl extends PGoTLANode {
	
	public static enum Type{
		INFIX,
		PREFIX,
		POSTFIX,
		NAMED,
		ID,
	}

	private PGoTLAIdentifier name;
	private Type type;
	private int arity;
	
	private PGoTLAOpDecl(SourceLocation location, PGoTLAIdentifier name, Type type, int arity) {
		super(location);
		this.name = name;
		this.type = type;
		this.arity = arity;
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTLANodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public static PGoTLAOpDecl Infix(SourceLocation location, PGoTLAIdentifier name) {
		return new PGoTLAOpDecl(location, name, Type.INFIX, 2);
	}
	
	public static PGoTLAOpDecl Prefix(SourceLocation location, PGoTLAIdentifier name) {
		return new PGoTLAOpDecl(location, name, Type.PREFIX, 1);
	}
	
	public static PGoTLAOpDecl Postfix(SourceLocation location, PGoTLAIdentifier name) {
		return new PGoTLAOpDecl(location, name, Type.POSTFIX, 1);
	}
	
	public static PGoTLAOpDecl Named(SourceLocation location, PGoTLAIdentifier name, int arity) {
		return new PGoTLAOpDecl(location, name, Type.NAMED, arity);
	}
	
	public static PGoTLAOpDecl Id(SourceLocation location, PGoTLAIdentifier name) {
		return new PGoTLAOpDecl(location, name, Type.ID, 0);
	}

	public PGoTLAIdentifier getName() {
		return name;
	}

	public Type getType() {
		return type;
	}

	public int getArity() {
		return arity;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + arity;
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + ((type == null) ? 0 : type.hashCode());
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
		PGoTLAOpDecl other = (PGoTLAOpDecl) obj;
		if (arity != other.arity)
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (type != other.type)
			return false;
		return true;
	}

}
