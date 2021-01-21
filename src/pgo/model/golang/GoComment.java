package pgo.model.golang;

import java.util.Objects;

/**
 * A Golang comment
 *
 */
public class GoComment extends GoStatement {
	private final String comment;

	public GoComment(String comment) {
		this.comment = comment;
	}
	
	public String getComment() {
		return comment;
	}

	@Override
	public <T, E extends Throwable> T accept(GoStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoComment comment1 = (GoComment) o;
		return Objects.equals(comment, comment1.comment);
	}

	@Override
	public int hashCode() {

		return Objects.hash(comment);
	}
}
