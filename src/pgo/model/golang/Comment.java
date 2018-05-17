package pgo.model.golang;

import java.util.Collections;
import java.util.List;
import java.util.Vector;

/**
 * A Golang comment
 *
 */
public class Comment extends Statement {
	private List<String> comment;
	// whether this is a block comment (true) with /* and */ or line comment
	// with "//"
	private boolean block;

	public Comment(List<String> comment, boolean b) {
		this.comment = comment;
		this.block = b;
	}

	// Convenience constructor used when there is only one line of comment.
	public Comment(String comment, boolean block) {
		this.comment = Collections.singletonList(comment);
		this.block = block;
	}

	public List<String> getComment() {
		return new Vector<>(comment);
	}

	public void addComment(String c) {
		this.comment.add(c);
	}

	public void removeComment(String c) {
		this.comment.remove(c);
	}

	public boolean getIsBlock() {
		return this.block;
	}

	public void setIsBlock(boolean b) {
		this.block = b;
	}

	@Override
	public List<String> toGo() {
		Vector<String> ret = new Vector<>();
		String linePrefix = block? " * " : "// ";
		
		if (block) {
			ret.add("/**");
		}
		for (String c : comment ) {
			ret.add(linePrefix + c);
		}
		if (block) {
			ret.add("**/");
		}
		return ret;
	}
}
