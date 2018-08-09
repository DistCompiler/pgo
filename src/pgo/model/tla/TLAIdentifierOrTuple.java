package pgo.model.tla;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

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
public class TLAIdentifierOrTuple extends TLANode {
	
	private List<TLAIdentifier> ids;
	private boolean tuple;
	
	private TLAIdentifierOrTuple(SourceLocation location, List<TLAIdentifier> ids, boolean isTuple) {
		super(location);
		this.ids = ids;
		this.tuple = isTuple;
	}
	
	@Override
	public TLAIdentifierOrTuple copy() {
		return new TLAIdentifierOrTuple(getLocation(), ids.stream().map(TLAIdentifier::copy).collect(Collectors.toList()), tuple);
	}
	
	@Override
	public <T, E extends Throwable> T accept(TLANodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public static TLAIdentifierOrTuple Identifier(TLAIdentifier id) {
		return new TLAIdentifierOrTuple(id.getLocation(), Collections.singletonList(id), false);
	}
	
	public static TLAIdentifierOrTuple Tuple(SourceLocation location, List<TLAIdentifier> ids) {
		return new TLAIdentifierOrTuple(location, ids, true);
	}
	
	public boolean isTuple() {
		return tuple;
	}
	
	public TLAIdentifier getId() {
		if(ids.size() != 1 || tuple) {
			throw new RuntimeException("tried to treat an identifier tuple as an identifier: was "+ids);
		}
		return ids.get(0);
	}
	
	public List<TLAIdentifier> getTuple(){
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
		TLAIdentifierOrTuple other = (TLAIdentifierOrTuple) obj;
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
