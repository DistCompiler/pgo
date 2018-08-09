package pgo.model.golang;

public class GoContinue extends GoStatement {

	@Override
	public <T, E extends Throwable> T accept(GoStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object other){
		return other instanceof GoContinue;
	}

	@Override
	public int hashCode(){
		return 0;
	}
}
