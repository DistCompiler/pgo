package pgo.model.tla;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST PlusCalNode, representing the kinds of things you can find in
 * TLA operator definition parameter lists. The special cases are usually
 * used for higher-order operators.
 *
 */
public class TLAOpDecl extends TLANode {
	
	public static enum Type{
		INFIX,
		PREFIX,
		POSTFIX,
		NAMED,
		ID,
	}

	private TLAIdentifier name;
	private Type type;
	private int arity;
	
	private TLAOpDecl(SourceLocation location, TLAIdentifier name, Type type, int arity) {
		super(location);
		this.name = name;
		this.type = type;
		this.arity = arity;
	}
	
	@Override
	public TLAOpDecl copy() {
		return new TLAOpDecl(getLocation(), name.copy(), type, arity);
	}
	
	@Override
	public <T, E extends Throwable> T accept(TLANodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public static TLAOpDecl Infix(SourceLocation location, TLAIdentifier name) {
		return new TLAOpDecl(location, name, Type.INFIX, 2);
	}
	
	public static TLAOpDecl Prefix(SourceLocation location, TLAIdentifier name) {
		return new TLAOpDecl(location, name, Type.PREFIX, 1);
	}
	
	public static TLAOpDecl Postfix(SourceLocation location, TLAIdentifier name) {
		return new TLAOpDecl(location, name, Type.POSTFIX, 1);
	}
	
	public static TLAOpDecl Named(SourceLocation location, TLAIdentifier name, int arity) {
		return new TLAOpDecl(location, name, Type.NAMED, arity);
	}
	
	public static TLAOpDecl Id(SourceLocation location, TLAIdentifier name) {
		return new TLAOpDecl(location, name, Type.ID, 0);
	}

	public TLAIdentifier getName() {
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
		TLAOpDecl other = (TLAOpDecl) obj;
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
