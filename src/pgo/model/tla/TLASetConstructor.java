package pgo.model.tla;

import pgo.util.SourceLocation;

import java.util.List;
import java.util.stream.Collectors;

/**
 * 
 * PlusCalWith TLAParser, this will always be the result of parsing an explicit set constructor:
 * 
 * { <expr>, <expr>, ... }
 *
 */
public class TLASetConstructor extends TLAExpression {

	private final List<TLAExpression> contents;
	
	public TLASetConstructor(SourceLocation location, List<TLAExpression> contents) {
		super(location);
		this.contents = contents;
	}
	
	@Override
	public TLASetConstructor copy() {
		return new TLASetConstructor(getLocation(), contents.stream().map(TLAExpression::copy).collect(Collectors.toList()));
	}

	public List<TLAExpression> getContents() {
		return contents;
	}

	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((contents == null) ? 0 : contents.hashCode());
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
		TLASetConstructor other = (TLASetConstructor) obj;
		if (contents == null) {
			return other.contents == null;
		} else return contents.equals(other.contents);
	}

}
