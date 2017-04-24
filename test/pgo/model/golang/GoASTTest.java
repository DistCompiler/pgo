package pgo.model.golang;

import static org.junit.Assert.assertEquals;

import java.util.Vector;

import org.junit.Test;

public class GoASTTest {

	@Test
	public void testComments() {
		Vector<String> cStrs = new Vector<String>();
		Vector<String> expected = new Vector<String>();

		cStrs.add("comment1");
		expected.add("// comment1");
		GoAST.Comment c = new GoAST.Comment(cStrs, false);
		assertEquals(expected, c.toGo());

		c.addComment("comment2");
		expected.add("// comment2");
		assertEquals(expected, c.toGo());

		c.removeComment("comment1");
		expected.remove(0);
		assertEquals(expected, c.toGo());

		c.removeComment("comment2");
		expected.remove(0);
		assertEquals(expected, c.toGo());

		c = new GoAST.Comment(cStrs, true);
		expected.add("/**");
		expected.add(" * comment1");
		expected.add("**/");
		assertEquals(expected, c.toGo());

		c.addComment("comment2");
		expected.add(2, " * comment2");
		assertEquals(expected, c.toGo());

		c.removeComment("comment1");
		c.removeComment("comment2");
		expected.remove(1);
		expected.remove(1);
		assertEquals(expected, c.toGo());
	}

}
