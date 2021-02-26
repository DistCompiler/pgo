package pgo.model.tla;

import pgo.util.SourceLocation;

import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

/**
 * 
 * TLA AST PlusCalNode:
 * 
 * op(<expr>, <expr>, ...)
 *
 */
public class TLAOperatorCall extends TLAExpression {

	private final TLAIdentifier name;
	private final List<TLAExpression> args;
	private final List<TLAGeneralIdentifierPart> prefix;
	private TLADefinitionOne refersTo;
	
	public TLAOperatorCall(SourceLocation location, TLAIdentifier name, List<TLAGeneralIdentifierPart> prefix, List<TLAExpression> args) {
		super(location);
		this.name = name;
		this.args = args;
		this.prefix = prefix;
	}

	public void setRefersTo(TLADefinitionOne refersTo) {
		this.refersTo = refersTo;
	}

	public TLADefinitionOne getRefersTo() {
		return refersTo;
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
        return this.getName().equals(other.getName()) &&
				Objects.equals(this.getArgs(), other.getArgs()) &&
				Objects.equals(this.getPrefix(), other.getPrefix());
	}

}
