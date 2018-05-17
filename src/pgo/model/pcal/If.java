package pgo.model.pcal;

import java.util.List;

import pgo.model.tla.PGoTLAExpression;
import pgo.util.SourceLocation;

public class If extends Statement {
	
	PGoTLAExpression condition;
	List<Statement> yes;
	List<Statement> no;
	
	public If(SourceLocation location, PGoTLAExpression condition, List<Statement> yes, List<Statement> no) {
		super(location);
		this.condition = condition;
		this.yes = yes;
		this.no = no;
	}
	
	public PGoTLAExpression getCondition() {
		return condition;
	}
	
	public List<Statement> getYes(){
		return yes;
	}
	
	public List<Statement> getNo(){
		return no;
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((condition == null) ? 0 : condition.hashCode());
		result = prime * result + ((no == null) ? 0 : no.hashCode());
		result = prime * result + ((yes == null) ? 0 : yes.hashCode());
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
		If other = (If) obj;
		if (condition == null) {
			if (other.condition != null)
				return false;
		} else if (!condition.equals(other.condition))
			return false;
		if (no == null) {
			if (other.no != null)
				return false;
		} else if (!no.equals(other.no))
			return false;
		if (yes == null) {
			if (other.yes != null)
				return false;
		} else if (!yes.equals(other.yes))
			return false;
		return true;
	}

}
