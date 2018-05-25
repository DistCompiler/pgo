package pgo.model.golang;

public class InterfaceType extends Type {

	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public boolean equals(Object other) {
		// TODO Auto-generated method stub
		return false;
	}

}
