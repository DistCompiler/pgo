package pgo.model.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.Vector;

import org.junit.Test;

import pgo.model.intermediate.PGoPrimitiveType.PGoBool;
import pgo.model.intermediate.PGoPrimitiveType.PGoInt;
import pgo.model.intermediate.PGoPrimitiveType.PGoString;
import pgo.model.intermediate.PGoPrimitiveType.PGoVoid;
import pgo.model.intermediate.PGoType;
import pgo.parser.PGoParseException;

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
}
