package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST Node:
 * 
 * << <expr>, <expr>, ... >>
 *
 */
public class PGoTLATuple extends PGoTLAExpression {

	private List<PGoTLAExpression> elements;
	
	public PGoTLATuple(SourceLocation location, List<PGoTLAExpression> elements) {
		super(location);
		this.elements = elements;
	}
	
	@Override
	public PGoTLATuple copy() {
		return new PGoTLATuple(getLocation(), elements.stream().map(PGoTLAExpression::copy).collect(Collectors.toList()));
	}
	
	public List<PGoTLAExpression> getElements(){
		return elements;
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTLAExpressionVisitor<T, E> v) throws E {
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
		PGoTLATuple other = (PGoTLATuple) obj;
		if (elements == null) {
			if (other.elements != null)
				return false;
		} else if (!elements.equals(other.elements))
			return false;
		return true;
	}

}
