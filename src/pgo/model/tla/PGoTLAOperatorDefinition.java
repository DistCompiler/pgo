package pgo.model.tla;

import java.util.List;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST Node representing a defined operator.
 * 
 * op(...) == ...
 *
 */
public class PGoTLAOperatorDefinition extends PGoTLAUnit {
	private PGoTLAIdentifier name;
	private List<PGoTLAOpDecl> args;
	private PGoTLAExpression body;
	private boolean local;
	
	public PGoTLAOperatorDefinition(SourceLocation location, PGoTLAIdentifier name, List<PGoTLAOpDecl> args, PGoTLAExpression body, boolean isLocal) {
		super(location);
		this.name = name;
		this.args = args;
		this.body = body;
		this.local = isLocal;
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTLAUnitVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public PGoTLAIdentifier getName() {
		return name;
	}

	public List<PGoTLAOpDecl> getArgs() {
		return args;
	}

	public PGoTLAExpression getBody() {
		return body;
	}
	
	public boolean isLocal() {
		return local;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((args == null) ? 0 : args.hashCode());
		result = prime * result + ((body == null) ? 0 : body.hashCode());
		result = prime * result + (local ? 1231 : 1237);
		result = prime * result + ((name == null) ? 0 : name.hashCode());
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
		PGoTLAOperatorDefinition other = (PGoTLAOperatorDefinition) obj;
		if (args == null) {
			if (other.args != null)
				return false;
		} else if (!args.equals(other.args))
			return false;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		if (local != other.local)
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		return true;
	}

}
