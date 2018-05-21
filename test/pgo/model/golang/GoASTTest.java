package pgo.model.golang;

import static org.junit.Assert.assertEquals;

import java.util.Collections;
import java.util.List;
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
		Vector<String> cStrs = new Vector<>();
		Vector<String> expected = new Vector<>();

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
		// we don't care about for loops with more than 1 expression; only
		// range-based and condition-based loops are compiled
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
		Function f = new Function("foo", new PGoPrimitiveType.PGoVoid(),
				new Vector<>(), new Vector<>(), new Vector<>());
		Vector<String> expected = new Vector<>();
		expected.add("func foo()  {");
		expected.add("}");
		assertEquals(expected, f.toGo());

		Vector<ParameterDeclaration> ps = new Vector<>();
		ps.add(new ParameterDeclaration("p1", new PGoPrimitiveType.PGoNatural()));
		f = new Function("foo", new PGoPrimitiveType.PGoVoid(), ps, new Vector<>(), new Vector<>());
		expected.remove(0);
		expected.add(0, "func foo(p1 uint64)  {");
		assertEquals(expected, f.toGo());

		ps.add(new ParameterDeclaration("p2", new PGoCollectionType.PGoSet("int")));
		f = new Function("foo", new PGoPrimitiveType.PGoVoid(), ps,
				new Vector<>(), new Vector<>());
		expected.remove(0);
		expected.add(0, "func foo(p1 uint64, p2 datatypes.Set)  {");
		assertEquals(expected, f.toGo());

		f = new Function("foo", new PGoPrimitiveType.PGoInt(), ps, new Vector<>(), new Vector<>());
		expected.remove(0);
		expected.add(0, "func foo(p1 uint64, p2 datatypes.Set) int {");
		assertEquals(expected, f.toGo());

		Vector<VariableDeclaration> vs = new Vector<>();
		vs.add(new VariableDeclaration("var1", new PGoPrimitiveType.PGoDecimal(),
				new SimpleExpression(new Vector<>()), false, false, false));
		f = new Function("foo", new PGoPrimitiveType.PGoInt(), ps, vs, new Vector<>());
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
		FunctionCall fc = new FunctionCall("foo", new Vector<>());
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
		assertEquals("goto L", g.toGo().get(0));
	}

	@Test
	public void testIf() {
		If i = new If(new Token("x > 0"), body, new Vector<>());
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
		AnonymousFunction f = new AnonymousFunction(PGoType.inferFromGoTypeName("bool"),
				new Vector<>(), new Vector<>(), funcBody, new Vector<>());
		i.setCond(f);
		expected.set(0, "if func() bool {");
		expected.insertElementAt("\tbar()", 1);
		expected.insertElementAt("\treturn x > 0", 2);
		expected.insertElementAt("}() {", 3);
		assertEquals(expected, i.toGo());
	}

	@Test
	public void testImports() {
		Imports im = new Imports();
		Vector<String> expected = new Vector<>();

		assertEquals(expected, im.toGo());

		im.addImport("pkg1");
		expected.add("import \"pkg1\"");
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
		assertEquals("L:", l.toGo().get(0));
	}

	@Test
	public void testParameterDeclaration() {
		ParameterDeclaration pd = new ParameterDeclaration("p1", new PGoPrimitiveType.PGoInt());
		assertEquals(1, pd.toGo().size());
		assertEquals("p1 int", pd.toGo().get(0));
		assertEquals(new Vector<>(Collections.singletonList("p1 int")), pd.toGo());
	}

	@Test
	public void testReturn() {
		Return r = new Return(null);
		assertEquals(1, r.toGo().size());
		assertEquals("return", r.toGo().get(0));

		r = new Return(new Token("ret"));
		assertEquals(1, r.toGo().size());
		assertEquals("return ret", r.toGo().get(0));
	}

	@Test
	public void testSelect() {
		Vector<Expression> cases = new Vector<>();
		cases.add(new Token("<-chan1"));
		cases.add(new Token("<-chan2"));
		List<List<Statement>> body = new Vector<>();
		Vector<Statement> b1 = new Vector<>();
		b1.add(new Token("x = 0"));
		body.add(b1);
		Vector<Statement> b2 = new Vector<>();
		b2.add(new Token("x = 1"));
		body.add(b2);
		Select s = new Select(cases, body);
		Vector<String> expected = new Vector<>();
		expected.add("select {");
		expected.add("case <-chan1:");
		expected.add("\tx = 0");
		expected.add("case <-chan2:");
		expected.add("\tx = 1");
		expected.add("}");
		assertEquals(expected, s.toGo());
		cases.add(new Token("<-chan3"));
		Vector<Statement> b3 = new Vector<>();
		b3.add(new Token("x = 2"));
		body.add(b3);
		s.setBodies(body);
		s.setCases(cases);
		expected.remove(expected.size() - 1);
		expected.add("case <-chan3:");
		expected.add("\tx = 2");
		expected.add("}");
		assertEquals(expected, s.toGo());
	}

	@Test
	public void testSimpleExpression() {
		Vector<Expression> toks = new Vector<>();
		toks.add(new Token("x"));
		toks.add(new Token(" = "));
		toks.add(new Token("2"));
		SimpleExpression se = new SimpleExpression(toks);
		Vector<String> expected = new Vector<>();
		expected.add("x = 2");
		assertEquals(expected, se.toGo());

		// test multiline expression
		toks = new Vector<>();
		Vector<Statement> body = new Vector<>();
		body.add(new Return(new Token("1")));
		AnonymousFunction f = new AnonymousFunction(PGoType.inferFromGoTypeName("int"),
				new Vector<>(), new Vector<>(), body, new Vector<>());
		toks.add(f);
		toks.add(new Token(" + "));
		toks.add(new Token("1"));
		se = new SimpleExpression(toks);
		expected.set(0, "func() int {");
		expected.add("\treturn 1");
		expected.add("}() + 1");
		assertEquals(expected, se.toGo());
	}

	@Test
	public void testTokenExpression() {
		Token te = new Token("");
		assertEquals(1, te.toGo().size());
		assertEquals("", te.toGo().get(0));

		te.setExpressions("var");
		assertEquals(1, te.toGo().size());
		assertEquals("var", te.toGo().get(0));

		Token t2 = new Token("[2]");

		te.merge(t2);

		assertEquals(1, te.toGo().size());
		assertEquals("var[2]", te.toGo().get(0));
	}

	@Test
	public void testVariableDeclaration() {
		VariableDeclaration vd = new VariableDeclaration("var1",
				new PGoPrimitiveType.PGoDecimal(), null, false, false, false);
		Vector<String> expected = new Vector<>();
		expected.add("var var1 float64");
		assertEquals(expected, vd.toGo());

		Vector<Expression> toks = new Vector<>();
		toks.add(new Token("1"));
		vd = new VariableDeclaration("var2", new PGoCollectionType.PGoMap("String", "boolean"),
				new SimpleExpression(toks), false, false, false);
		expected = new Vector<>();
		expected.add("var var2 datatypes.Map = 1");
		assertEquals(expected, vd.toGo());

		// TODO assert the init codes
	}
}
