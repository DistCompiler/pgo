package pgo.model.pcal;

import java.util.List;
import java.util.stream.Collectors;

import pgo.model.tla.TLAExpression;
import pgo.util.SourceLocation;

public class PlusCalMacroCall extends PlusCalStatement {
	
	private String target;
	private List<TLAExpression> arguments;
	
	public PlusCalMacroCall(SourceLocation location, String target, List<TLAExpression> arguments) {
		super(location);
		this.target = target;
		this.arguments = arguments;
	}
	
	@Override
	public PlusCalMacroCall copy() {
		return new PlusCalMacroCall(getLocation(), target, arguments.stream().map(TLAExpression::copy).collect(Collectors.toList()));
	}
	
	public String getTarget() {
		return target;
	}
	
	public List<TLAExpression> getArguments(){
		return arguments;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((arguments == null) ? 0 : arguments.hashCode());
		result = prime * result + ((target == null) ? 0 : target.hashCode());
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
		PlusCalMacroCall other = (PlusCalMacroCall) obj;
		if (arguments == null) {
			if (other.arguments != null)
				return false;
		} else if (!arguments.equals(other.arguments))
			return false;
		if (target == null) {
			return other.target == null;
		} else return target.equals(other.target);
	}

}
