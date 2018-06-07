package pgo.model.golang;

import java.util.Objects;

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
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		Comment comment1 = (Comment) o;
		return Objects.equals(comment, comment1.comment);
	}

	@Override
	public int hashCode() {

		return Objects.hash(comment);
	}
}
