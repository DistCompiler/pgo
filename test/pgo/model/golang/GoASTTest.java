package pgo.model.golang;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Vector;

import org.junit.Test;

import pgo.model.intermediate.PGoCollectionType;
import pgo.model.intermediate.PGoPrimitiveType;

public class GoASTTest {

	@Test
	public void testComments() {
		Vector<String> cStrs = new Vector<String>();
		Vector<String> expected = new Vector<String>();

		cStrs.add("comment1");
		expected.add("// comment1");
		Comment c = new Comment(cStrs, false);
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

		cStrs.clear();
		cStrs.add("comment1");
		c = new Comment(cStrs, true);
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

	@Test
	public void testImports() {
		Imports im = new Imports();
		Vector<String> expected = new Vector<String>();

		assertEquals(expected, im.toGo());
		
		im.addImport("pkg1");
		expected.add("import pkg1");
		assertEquals(expected, im.toGo());
		
		expected.clear();
		im.addImport("pkg3");
		expected.add("import (");
		expected.add("\tpkg1");
		expected.add("\tpkg3");
		expected.add(")");
		assertEquals(expected, im.toGo());
		
		im.addImport("pkg3");
		assertEquals(expected, im.toGo());
		
		im.addImport("pkg2");
		expected.add(2,"\tpkg2");
		assertEquals(expected, im.toGo());
	}

	@Test
	public void testParameterDeclaration() {
		ParameterDeclaration pd = new ParameterDeclaration("p1", new PGoPrimitiveType.PGoInt());
		assertEquals("p1 int", pd.toGoExpr());
		assertEquals(new Vector<String>(Arrays.asList(new String[] { "p1 int" })), pd.toGo());
	}

	@Test
	public void testVariableDeclaration() {
		VariableDeclaration vd = new VariableDeclaration("var1", new PGoPrimitiveType.PGoDecimal(),
				new SimpleExpression(), new Vector<Statement>());
		Vector<String> expected = new Vector<String>();
		expected.add("var var1 float64 = ");
		assertEquals(expected, vd.toGo());

		vd = new VariableDeclaration("var2", new PGoCollectionType.PGoMap("String", "boolean"),
				new SimpleExpression(), new Vector<Statement>());
		expected = new Vector<String>();
		expected.add("var var2 map[string]bool = ");
		assertEquals(expected, vd.toGo());

		// TODO assert the init codes
	}

	@Test
	public void testFunction() {
		Function f = new Function("foo", new PGoPrimitiveType.PGoVoid(), new Vector<ParameterDeclaration>(),
				new Vector<VariableDeclaration>(), new Vector<Statement>());
		Vector<String> expected = new Vector<String>();
		expected.add("func foo()  {");
		expected.add("}");
		assertEquals(expected, f.toGo());
		
		Vector<ParameterDeclaration> ps = new Vector<ParameterDeclaration>();
		ps.add(new ParameterDeclaration("p1", new PGoPrimitiveType.PGoNatural()));
		f = new Function("foo", new PGoPrimitiveType.PGoVoid(), ps,
				new Vector<VariableDeclaration>(), new Vector<Statement>());
		expected.remove(0);
		expected.add(0, "func foo(p1 uint64)  {");
		assertEquals(expected, f.toGo());

		ps.add(new ParameterDeclaration("p2", new PGoCollectionType.PGoSet("int")));
		f = new Function("foo", new PGoPrimitiveType.PGoVoid(), ps, new Vector<VariableDeclaration>(),
				new Vector<Statement>());
		expected.remove(0);
		expected.add(0, "func foo(p1 uint64, p2 Set)  {");
		assertEquals(expected, f.toGo());
		
		f = new Function("foo", new PGoPrimitiveType.PGoInt(), ps,
				new Vector<VariableDeclaration>(), new Vector<Statement>());
		expected.remove(0);
		expected.add(0, "func foo(p1 uint64, p2 Set) int {");
		assertEquals(expected, f.toGo());

		Vector<VariableDeclaration> vs = new Vector<VariableDeclaration>();
		vs.add(new VariableDeclaration("var1", new PGoPrimitiveType.PGoDecimal(), new SimpleExpression(),
				new Vector<Statement>()));
		f = new Function("foo", new PGoPrimitiveType.PGoInt(), ps, vs, new Vector<Statement>());
		expected.remove(1);
		for (VariableDeclaration v : vs) {
			for (String s : v.toGo()) {
				expected.add("\t" + s);
			}
		}
		expected.add("}");
		assertEquals(expected, f.toGo());

		// TODO function body
	}
}
