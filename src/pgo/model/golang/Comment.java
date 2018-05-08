package pgo.model.golang;

/**
 * A Golang comment
 *
 */
public class Comment extends Statement {
	private String comment;

	public Comment(String comment) {
		this.comment = comment;
	}
	
	public String getComment() {
		return comment;
	}

	@Override
	public <T> T accept(Visitor<T> v) {
		return v.visit(this);
	}
	
}
