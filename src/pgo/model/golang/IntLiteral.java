package pgo.model.golang;

public class IntLiteral extends Expression {

	private int value;

	public IntLiteral(int value) {
		this.value = value;
	}
	
	public int getValue() {
		return value;
	}

	@Override
	public <T> T accept(Visitor<T> v) {
		return v.visit(this);
	}

}
