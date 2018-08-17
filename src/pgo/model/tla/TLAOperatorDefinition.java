package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST PlusCalNode representing a defined operator.
 * 
 * op(...) == ...
 *
 */
public class TLAOperatorDefinition extends TLAUnit {
	private TLAIdentifier name;
	private List<TLAOpDecl> args;
	private TLAExpression body;
	private boolean local;
	
	public TLAOperatorDefinition(SourceLocation location, TLAIdentifier name, List<TLAOpDecl> args, TLAExpression body, boolean isLocal) {
		super(location);
		this.name = name;
		this.args = args;
		this.body = body;
		this.local = isLocal;
	}
	
	@Override
	public TLAOperatorDefinition copy() {
		return new TLAOperatorDefinition(getLocation(), name.copy(), args.stream().map(TLAOpDecl::copy).collect(Collectors.toList()), body.copy(), local);
	}
	
	@Override
	public <T, E extends Throwable> T accept(TLAUnitVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public TLAIdentifier getName() {
		return name;
	}

	public List<TLAOpDecl> getArgs() {
		return args;
	}

	public TLAExpression getBody() {
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
		TLAOperatorDefinition other = (TLAOperatorDefinition) obj;
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
			return other.name == null;
		} else return name.equals(other.name);
	}

}
