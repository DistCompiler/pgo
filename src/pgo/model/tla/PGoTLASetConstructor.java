package pgo.model.tla;

import java.util.List;

import pgo.util.SourceLocation;

/**
 * 
 * With TLAParser, this will always be the result of parsing an explicit set constructor:
 * 
 * { <expr>, <expr>, ... }
 *
 */
public class PGoTLASetConstructor extends PGoTLAExpression {

	private List<PGoTLAExpression> contents;
	
	public PGoTLASetConstructor(SourceLocation location, List<PGoTLAExpression> contents) {
		super(location);
		this.contents = contents;
	}

	public List<PGoTLAExpression> getContents() {
		return contents;
	}

	@Override
	public <T> T accept(Visitor<T> v) {
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
		PGoTLASetConstructor other = (PGoTLASetConstructor) obj;
		if (contents == null) {
			if (other.contents != null)
				return false;
		} else if (!contents.equals(other.contents))
			return false;
		return true;
	}

}
