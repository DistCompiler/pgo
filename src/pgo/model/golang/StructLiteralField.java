package pgo.model.golang;

public class StructLiteralField extends Node {

	private String name;
	private Expression value;

	public StructLiteralField(String name, Expression value){
		this.name = name;
		this.value = value;
	}

	public String getName() {
		return name;
	}

	public Expression getValue() {
		return value;
	}

	@Override
	public <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
