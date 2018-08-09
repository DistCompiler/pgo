package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST PlusCalNode:
 * 
 * op(<expr>, <expr>, ...)
 *
 */
public class TLAOperatorCall extends TLAExpression {

	private TLAIdentifier name;
	private List<TLAExpression> args;
	private List<TLAGeneralIdentifierPart> prefix;
	
	public TLAOperatorCall(SourceLocation location, TLAIdentifier name, List<TLAGeneralIdentifierPart> prefix, List<TLAExpression> args) {
		super(location);
		this.name = name;
		this.args = args;
		this.prefix = prefix;
	}
	
	@Override
	public TLAOperatorCall copy() {
		return new TLAOperatorCall(getLocation(), name.copy(),
				prefix.stream().map(TLAGeneralIdentifierPart::copy).collect(Collectors.toList()),
				args.stream().map(TLAExpression::copy).collect(Collectors.toList()));
	}
	
	public TLAIdentifier getName() {
		return name;
	}
	
	public List<TLAExpression> getArgs(){
		return args;
	}
	
	public List<TLAGeneralIdentifierPart> getPrefix(){
		return prefix;
	}
	
	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((args == null) ? 0 : args.hashCode());
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + ((prefix == null) ? 0 : prefix.hashCode());
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
		TLAOperatorCall other = (TLAOperatorCall) obj;
		if (args == null) {
			if (other.args != null)
				return false;
		} else if (!args.equals(other.args))
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (prefix == null) {
			if (other.prefix != null)
				return false;
		} else if (!prefix.equals(other.prefix))
			return false;
		return true;
	}

}
