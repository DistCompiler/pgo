package pgo.model.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.Vector;

import org.junit.Test;

import pcal.AST.PVarDecl;
import pcal.AST.Procedure;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoPrimitiveType.PGoBool;
import pgo.model.intermediate.PGoPrimitiveType.PGoInt;
import pgo.model.intermediate.PGoPrimitiveType.PGoString;
import pgo.model.intermediate.PGoPrimitiveType.PGoVoid;
import pgo.model.intermediate.PGoType;
import pgo.parser.PGoParseException;
import pgo.trans.PGoTransException;

public class AnnotatedFunctionTest {

	@Test
	public void testVoidFunction() throws PGoParseException {
		String[] parts;
		AnnotatedFunction fun;
		Vector<PGoType> argTypes ;
		
		parts = new String[] { "func", "fun()" };
		fun = AnnotatedFunction.parse(parts, 0);
		assertEquals(0, fun.getLine());
		assertEquals("fun", fun.getName());
		assertTrue(fun.getReturnType() instanceof PGoVoid);
		argTypes = fun.getArgTypes();
		assertEquals(0, argTypes.size());
		
		
		parts = new String[] { "func", "foo()", "int", "string" };
		fun = AnnotatedFunction.parse(parts, 2);
		assertEquals(2, fun.getLine());
		assertEquals("foo", fun.getName());
		assertTrue(fun.getReturnType() instanceof PGoVoid);
		argTypes = fun.getArgTypes();
		assertEquals(2, argTypes.size());
		assertTrue(argTypes.get(0) instanceof PGoInt);
		assertTrue(argTypes.get(1) instanceof PGoString);

		try {
			parts = new String[] { "func", "foo()", "wrongtype", "string" };
			AnnotatedFunction.parse(parts, 2);
			fail("Exception expected for unknown type");
		} catch (PGoParseException e) {

		}
	}

	@Test
	public void testReturnFunction() throws PGoParseException {
		String[] parts;
		AnnotatedFunction fun;
		Vector<PGoType> argTypes;

		parts = new String[] { "func", "int", "fun()" };
		fun = AnnotatedFunction.parse(parts, 0);
		assertEquals(0, fun.getLine());
		assertEquals("fun", fun.getName());
		assertTrue(fun.getReturnType() instanceof PGoInt);
		argTypes = fun.getArgTypes();
		assertEquals(0, argTypes.size());

		parts = new String[] { "func", "bool", "foo()", "int", "string" };
		fun = AnnotatedFunction.parse(parts, 2);
		assertEquals(2, fun.getLine());
		assertEquals("foo", fun.getName());
		assertTrue(fun.getReturnType() instanceof PGoBool);
		argTypes = fun.getArgTypes();
		assertEquals(2, argTypes.size());
		assertTrue(argTypes.get(0) instanceof PGoInt);
		assertTrue(argTypes.get(1) instanceof PGoString);

		try {
			parts = new String[] { "func", "bool", "foo()", "wrongtype", "string" };
			AnnotatedFunction.parse(parts, 2);
			fail("Exception expected for unknown type");
		} catch (PGoParseException e) {

		}

		try {
			parts = new String[] { "func", "unknowntype", "foo()", "int", "string" };
			AnnotatedFunction.parse(parts, 2);
			fail("Exception expected for unknown type");
		} catch (PGoParseException e) {

		}
	}

	@Test
	public void testFillFunction() throws PGoParseException, PGoTransException {
		PGoFunction f;
		AnnotatedFunction af;

		Procedure p;
		PVarDecl pv;

		p = new Procedure();
		p.params = new Vector();
		p.decls = new Vector();
		p.name = "func";
		f = PGoFunction.convert(p);
		af = AnnotatedFunction.parse(new String[] { "func", "func()" }, 1);
		af.fillFunction(f);
		assertEquals(0, f.getParams().size());
		assertEquals(PGoType.VOID, f.getReturnType());

		pv = new PVarDecl();
		pv.var = "Param1";
		p.params.add(pv);
		f = PGoFunction.convert(p);
		try {
			af.fillFunction(f);
			fail("Exception expected for parameter size mismatch");
		} catch (PGoTransException e) {

		}

		af = AnnotatedFunction.parse(new String[] { "func", "void", "func()", "int" }, 2);
		af.fillFunction(f);
		assertEquals(1, f.getParams().size());
		assertEquals(new PGoPrimitiveType.PGoInt(), f.getParam("Param1").getType());
		assertEquals(PGoType.VOID, f.getReturnType());

		pv = new PVarDecl();
		pv.var = "Param2";
		p.params.add(pv);
		f = PGoFunction.convert(p);

		af = AnnotatedFunction.parse(new String[] { "func", "boolean", "func()", "int", "string" }, 2);
		af.fillFunction(f);
		assertEquals(2, f.getParams().size());
		assertEquals(new PGoPrimitiveType.PGoInt(), f.getParam("Param1").getType());
		assertEquals(new PGoPrimitiveType.PGoString(), f.getParam("Param2").getType());
		assertEquals(new PGoPrimitiveType.PGoBool(), f.getReturnType());

	}
}
