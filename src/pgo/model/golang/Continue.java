package pgo.model.golang;

public class Continue extends Statement {

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object other){
		return other instanceof Continue;
	}

	@Override
	public int hashCode(){
		return 0;
	}
}
