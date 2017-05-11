package pgo.model.golang;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Vector;

import org.junit.Test;

import pgo.model.intermediate.PGoCollectionType;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoType;

public class GoASTTest {
	private static final Vector<Statement> body = new Vector<>();
	static {
		body.add(new FunctionCall("foo", new Vector<>()));
	}

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
	public void testFor() {
		// we don't care about for loops with more than 1 expression; only range-based and condition-based loops are compiled
		For f = new For(new Token("x > 0"), body);
		Vector<String> expected = new Vector<>();
		expected.add("x > 0");
		assertEquals(expected, f.getCond().toGo());
		expected.set(0, "for x > 0 {");
		expected.add("\tfoo()");
		expected.add("}");
		assertEquals(expected, f.toGo());
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
		f = new Function("foo", new PGoPrimitiveType.PGoVoid(), ps, new Vector<VariableDeclaration>(), new Vector<Statement>());
		expected.remove(0);
		expected.add(0, "func foo(p1 uint64)  {");
		assertEquals(expected, f.toGo());

		ps.add(new ParameterDeclaration("p2", new PGoCollectionType.PGoSet("int")));
		f = new Function("foo", new PGoPrimitiveType.PGoVoid(), ps, new Vector<VariableDeclaration>(), new Vector<Statement>());
		expected.remove(0);
		expected.add(0, "func foo(p1 uint64, p2 mapset.Set)  {");
		assertEquals(expected, f.toGo());

		f = new Function("foo", new PGoPrimitiveType.PGoInt(), ps, new Vector<VariableDeclaration>(), new Vector<Statement>());
		expected.remove(0);
		expected.add(0, "func foo(p1 uint64, p2 mapset.Set) int {");
		assertEquals(expected, f.toGo());

		Vector<VariableDeclaration> vs = new Vector<VariableDeclaration>();
		vs.add(new VariableDeclaration("var1", new PGoPrimitiveType.PGoDecimal(),
				new SimpleExpression(new Vector<Expression>()), false));
		f = new Function("foo", new PGoPrimitiveType.PGoInt(), ps, vs, new Vector<Statement>());
		expected.remove(1);
		for (VariableDeclaration v : vs) {
			for (String s : v.toGo()) {
				expected.add("\t" + s);
			}
		}
		expected.add("}");
		assertEquals(expected, f.toGo());

		f.setBody(body);
		expected.remove(expected.size() - 1);
		expected.add("\tfoo()");
		expected.add("}");
		assertEquals(expected, f.toGo());
	}

	@Test
	public void testFunctionCall() {
		FunctionCall fc = new FunctionCall("foo", new Vector<Expression>());
		Vector<String> expected = new Vector<>();
		expected.add("foo()");
		assertEquals(expected, fc.toGo());
		Vector<Expression> params = new Vector<>();
		params.add(new Token("bar"));
		params.add(new Token("baz"));
		fc.setParams(params);
		expected.set(0, "foo(bar, baz)");
		assertEquals(expected, fc.toGo());
		fc = new FunctionCall("foo", params, new Token("obj"));
		expected.set(0, "obj.foo(bar, baz)");
		assertEquals(expected, fc.toGo());
	}

	@Test
	public void testGoTo() {
		GoTo g = new GoTo("L");
		assertEquals(1, g.toGo().size());
		assertEquals("goto L", g.toGo().firstElement());
	}

	@Test
	public void testIf() {
		If i = new If(new Token("x > 0"), body, new Vector<Statement>());
		Vector<String> expected = new Vector<>();
		expected.add("if x > 0 {");
		expected.add("\tfoo()");
		expected.add("}");
		assertEquals(expected, i.toGo());
		Vector<Statement> el = new Vector<>();
		el.add(new Token("bar()"));
		i.setElse(el);
		expected.add(expected.remove(expected.size() - 1) + " else {");
		expected.add("\tbar()");
		expected.add("}");
		assertEquals(expected, i.toGo());
		Vector<Statement> funcBody = new Vector<>();
		funcBody.add(new Token("bar()"));
		funcBody.add(new Token("return x > 0"));
		AnonymousFunction f = new AnonymousFunction(PGoType.inferFromGoTypeName("bool"), new Vector<>(), new Vector<>(), funcBody,
				new Vector<>());
		i.setCond(f);
		expected.set(0, "if func() bool {");
		expected.insertElementAt("\tbar()", 1);
		expected.insertElementAt("\treturn x > 0", 2);
		expected.insertElementAt("}() {", 3);
		for (String s : i.toGo()) {
			System.out.println(s);
		}
		assertEquals(expected, i.toGo());
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
		expected.add("\t\"pkg1\"");
		expected.add("\t\"pkg3\"");
		expected.add(")");
		assertEquals(expected, im.toGo());

		im.addImport("pkg3");
		assertEquals(expected, im.toGo());

		im.addImport("pkg2");
		expected.add(2, "\t\"pkg2\"");
		assertEquals(expected, im.toGo());
	}

	@Test
	public void testLabel() {
		Label l = new Label("L");
		assertEquals(1, l.toGo().size());
		assertEquals("L:", l.toGo().firstElement());
	}

	@Test
	public void testParameterDeclaration() {
		ParameterDeclaration pd = new ParameterDeclaration("p1", new PGoPrimitiveType.PGoInt());
		assertEquals(1, pd.toGo().size());
		assertEquals("p1 int", pd.toGo().firstElement());
		assertEquals(new Vector<String>(Arrays.asList(new String[] { "p1 int" })), pd.toGo());
	}

	@Test
	public void testReturn() {
		Return r = new Return(null);
		assertEquals(1, r.toGo().size());
		assertEquals("return", r.toGo().firstElement());

		r = new Return(new Token("ret"));
		assertEquals(1, r.toGo().size());
		assertEquals("return ret", r.toGo().firstElement());
	}

	@Test
	public void testSelect() {
		// TODO
	}

	@Test
	public void testSimpleExpression() {
		// TODO
	}

	@Test
	public void testTokenExpression() {
		Token te = new Token("");
		assertEquals(1, te.toGo().size());
		assertEquals("", te.toGo().firstElement());

		te.setExpressions("var");
		assertEquals(1, te.toGo().size());
		assertEquals("var", te.toGo().firstElement());

		Token t2 = new Token("[2]");

		te.merge(t2);

		assertEquals(1, te.toGo().size());
		assertEquals("var[2]", te.toGo().firstElement());
	}

	@Test
	public void testVariableDeclaration() {
		VariableDeclaration vd = new VariableDeclaration("var1", new PGoPrimitiveType.PGoDecimal(), null, false);
		Vector<String> expected = new Vector<String>();
		expected.add("var var1 float64");
		assertEquals(expected, vd.toGo());

		Vector<Expression> toks = new Vector<Expression>();
		toks.add(new Token("1"));
		vd = new VariableDeclaration("var2", new PGoCollectionType.PGoMap("String", "boolean"), new SimpleExpression(toks),
				false);
		expected = new Vector<String>();
		expected.add("var var2 map[string]bool = 1");
		assertEquals(expected, vd.toGo());

		// TODO assert the init codes
	}
}
