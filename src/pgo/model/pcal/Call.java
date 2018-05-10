package pgo.model.pcal;

import java.util.List;

import pgo.model.tla.PGoTLAExpression;
import pgo.util.SourceLocation;

public class Call extends Statement {
	
	String target;
	List<PGoTLAExpression> arguments;
	
	public Call(SourceLocation location, String target, List<PGoTLAExpression> arguments) {
		super(location);
		this.target = target;
		this.arguments = arguments;
	}
	
	public String getTarget() {
		return target;
	}
	
	public List<PGoTLAExpression> getArguments(){
		return arguments;
	}

	@Override
	public <T> T accept(Visitor<T> v) {
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
		Call other = (Call) obj;
		if (arguments == null) {
			if (other.arguments != null)
				return false;
		} else if (!arguments.equals(other.arguments))
			return false;
		if (target == null) {
			if (other.target != null)
				return false;
		} else if (!target.equals(other.target))
			return false;
		return true;
	}

}
