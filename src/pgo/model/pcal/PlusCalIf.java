package pgo.model.pcal;

import java.util.List;
import java.util.stream.Collectors;

import pgo.model.tla.TLAExpression;
import pgo.util.SourceLocation;

public class PlusCalIf extends PlusCalStatement {
	
	TLAExpression condition;
	List<PlusCalStatement> yes;
	List<PlusCalStatement> no;
	
	public PlusCalIf(SourceLocation location, TLAExpression condition, List<PlusCalStatement> yes, List<PlusCalStatement> no) {
		super(location);
		this.condition = condition;
		this.yes = yes;
		this.no = no;
	}
	
	@Override
	public PlusCalIf copy() {
		return new PlusCalIf(getLocation(), condition.copy(),
				yes.stream().map(PlusCalStatement::copy).collect(Collectors.toList()),
				no.stream().map(PlusCalStatement::copy).collect(Collectors.toList()));
	}
	
	public TLAExpression getCondition() {
		return condition;
	}
	
	public List<PlusCalStatement> getYes(){
		return yes;
	}
	
	public List<PlusCalStatement> getNo(){
		return no;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalStatementVisitor<T, E> v) throws E {
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
		PlusCalIf other = (PlusCalIf) obj;
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
