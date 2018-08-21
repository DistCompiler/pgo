package pgo.model.golang.type;

import pgo.model.golang.GoNode;
import pgo.model.golang.GoNodeVisitor;

public abstract class GoType extends GoNode {
	
	@Override
	public abstract int hashCode();
	
	@Override
	public abstract boolean equals(Object other);
	
	public abstract <T, E extends Throwable> T accept(GoTypeVisitor<T, E> v) throws E;
	
	@Override
	public <T, E extends Throwable> T accept(GoNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
