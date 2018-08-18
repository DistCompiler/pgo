package pgo.model.tla;

import pgo.util.SourceLocation;

import java.util.List;
import java.util.stream.Collectors;

/**
 * 
 * TLA AST PlusCalNode:
 * 
 * << <expr>, <expr>, ... >>
 *
 */
public class TLATuple extends TLAExpression {

	private List<TLAExpression> elements;
	
	public TLATuple(SourceLocation location, List<TLAExpression> elements) {
		super(location);
		this.elements = elements;
	}
	
	@Override
	public TLATuple copy() {
		return new TLATuple(getLocation(), elements.stream().map(TLAExpression::copy).collect(Collectors.toList()));
	}
	
	public List<TLAExpression> getElements(){
		return elements;
	}
	
	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((elements == null) ? 0 : elements.hashCode());
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
		TLATuple other = (TLATuple) obj;
		if (elements == null) {
			return other.elements == null;
		} else return elements.equals(other.elements);
	}

}
