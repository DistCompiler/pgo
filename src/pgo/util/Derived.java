package pgo.util;

import java.util.ArrayList;
import java.util.List;

/**
 * 
 * Something that was derived from something else.
 * 
 * This helps us track where things came from in PGo if an error occurs.
 *
 */
public abstract class Derived implements Origin {
	List<Origin> origins;
	
	public Derived() {
		this.origins = new ArrayList<>();
	}
	
	public Derived addOrigin(Origin origin) {
		origins.add(origin);
		return this;
	}
	
	public List<Origin> getOrigins(){
		return origins;
	}
	
	public <T, E extends Throwable> T accept(OriginVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public abstract <T, E extends Throwable> T accept(DerivedVisitor<T, E> v) throws E;
	
}
