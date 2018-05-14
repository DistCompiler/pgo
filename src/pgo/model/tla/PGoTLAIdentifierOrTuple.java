package pgo.model.tla;

import java.util.Collections;
import java.util.List;

import pgo.util.SourceLocation;

/**
 * 
 * Some parts of the grammar can either result in a single identifier or 
 * a tuple of identifiers. This allows parts of the parser to return
 * the sum type-like result they expect.
 * 
 * a
 * or
 * << a, b, c >>
 *
 */
public class PGoTLAIdentifierOrTuple extends PGoTLANode {
	
	List<PGoTLAIdentifier> ids;
	boolean tuple;
	
	private PGoTLAIdentifierOrTuple(SourceLocation location, List<PGoTLAIdentifier> ids, boolean isTuple) {
		super(location);
		this.ids = ids;
		this.tuple = isTuple;
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTLANodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public static PGoTLAIdentifierOrTuple Identifier(PGoTLAIdentifier id) {
		return new PGoTLAIdentifierOrTuple(id.getLocation(), Collections.singletonList(id), false);
	}
	
	public static PGoTLAIdentifierOrTuple Tuple(SourceLocation location, List<PGoTLAIdentifier> ids) {
		return new PGoTLAIdentifierOrTuple(location, ids, true);
	}
	
	public boolean isTuple() {
		return tuple;
	}
	
	public PGoTLAIdentifier getId() {
		if(ids.size() != 1 || tuple) {
			throw new RuntimeException("tried to treat an identifier tuple as an identifier: was "+ids);
		}
		return ids.get(0);
	}
	
	public List<PGoTLAIdentifier> getTuple(){
		if(!tuple) {
			throw new RuntimeException("tried to tread an identifier as an identifier tuple: was "+ids);
		}
		return ids;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((ids == null) ? 0 : ids.hashCode());
		result = prime * result + (tuple ? 1231 : 1237);
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
		PGoTLAIdentifierOrTuple other = (PGoTLAIdentifierOrTuple) obj;
		if (ids == null) {
			if (other.ids != null)
				return false;
		} else if (!ids.equals(other.ids))
			return false;
		if (tuple != other.tuple)
			return false;
		return true;
	}

}
