package pgo.model.golang;

public class GoBreak extends GoStatement {

	@Override
	public <T, E extends Throwable> T accept(GoStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object other){
		return other instanceof GoBreak;
	}

	@Override
	public int hashCode(){
		return 0;
	}

}
