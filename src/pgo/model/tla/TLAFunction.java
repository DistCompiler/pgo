package pgo.model.tla;

import pgo.util.SourceLocation;

import java.util.List;
import java.util.stream.Collectors;

/**
 * 
 * TLA AST PlusCalNode:
 * 
 * [ a \in B, << c, d >> \in E |-> <expr> ]
 *
 */
public class TLAFunction extends TLAExpression {

	private final List<TLAQuantifierBound> args;
	private final TLAExpression body;

	public TLAFunction(SourceLocation location, List<TLAQuantifierBound> args, TLAExpression body) {
		super(location);
		this.args = args;
		this.body = body;
	}
	
	@Override
	public TLAFunction copy() {
		return new TLAFunction(getLocation(), args.stream().map(TLAQuantifierBound::copy).collect(Collectors.toList()), body.copy());
	}
	
	public List<TLAQuantifierBound> getArguments(){
		return args;
	}
	
	public TLAExpression getBody() {
		return body;
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
		result = prime * result + ((body == null) ? 0 : body.hashCode());
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
		TLAFunction other = (TLAFunction) obj;
		if (args == null) {
			if (other.args != null)
				return false;
		} else if (!args.equals(other.args))
			return false;
		if (body == null) {
			return other.body == null;
		} else return body.equals(other.body);
	}

}
