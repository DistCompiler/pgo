package pgo.model.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.junit.Test;

import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoPrimitiveType.PGoInt;
import pgo.model.intermediate.PGoPrimitiveType.PGoString;
import pgo.model.intermediate.PGoVariable;
import pgo.model.parser.AnnotatedVariable.ArgAnnotatedVariable;
import pgo.model.parser.AnnotatedVariable.ConstAnnotatedVariable;
import pgo.model.parser.AnnotatedVariable.VarAnnotatedVariable;
import pgo.model.type.PGoTypeGenerator;
import pgo.model.type.PGoTypeInt;
import pgo.model.type.PGoTypeString;
import pgo.model.type.PGoTypeVariable;
import pgo.parser.PGoParseException;
import pgo.trans.PGoTransException;

public class AnnotatedVariableTest {
	private static PGoTypeGenerator generator = new PGoTypeGenerator("test");

	@Test
	public void testConstVars() throws PGoParseException, PGoTransException {
		String[] parts;
		AnnotatedVariable var;
		ConstAnnotatedVariable cvar;

		parts = new String[] { "const", "x", "int", "2" };
		var = AnnotatedVariable.parse(0, parts, generator);
		assertTrue(var instanceof ConstAnnotatedVariable);
		assertEquals(0, var.getLine());
		cvar = (ConstAnnotatedVariable) var;
		assertEquals("x", cvar.getName());
		assertTrue(cvar.getType() instanceof PGoTypeInt);
		assertEquals("2", cvar.getVal());

		parts = new String[] { "const", "var_y", "string", "hababa" };
		var = AnnotatedVariable.parse(2, parts, generator);
		assertTrue(var instanceof ConstAnnotatedVariable);
		assertEquals(2, var.getLine());
		cvar = (ConstAnnotatedVariable) var;
		assertEquals("var_y", cvar.getName());
		assertTrue(cvar.getType() instanceof PGoTypeString);
		assertEquals("hababa", cvar.getVal());

		try {
			parts = new String[] { "const", "x", "int", "2", "extra" };
			AnnotatedVariable.parse(2, parts, generator);
			fail("Exception expected for extra argument");
		} catch (PGoParseException e) {

		}

		try {
			parts = new String[] { "const", "x" };
			AnnotatedVariable.parse(2, parts, generator);
			fail("Exception expected for missing argument");
		} catch (PGoParseException e) {

		}

		try {
			parts = new String[] { "const", "x", "wrongtype", "2" };
			AnnotatedVariable.parse(2, parts, generator);
			fail("Exception expected for unknown type");
		} catch (PGoTransException e) {

		}

	}

	@Test
	public void testArgVars() throws PGoParseException, PGoTransException {
		String[] parts;
		AnnotatedVariable var;
		ArgAnnotatedVariable avar;

		parts = new String[] { "arg", "x", "int" };
		var = AnnotatedVariable.parse(0, parts, generator);
		assertTrue(var instanceof ArgAnnotatedVariable);
		assertEquals(0, var.getLine());
		avar = (ArgAnnotatedVariable) var;
		assertEquals("x", avar.getName());
		assertTrue(avar.getType() instanceof PGoTypeInt);
		assertTrue(avar.isPositionalArg());

		parts = new String[] { "arg", "var_y", "string", "argname" };
		var = AnnotatedVariable.parse(2, parts, generator);
		assertTrue(var instanceof ArgAnnotatedVariable);
		assertEquals(2, var.getLine());
		avar = (ArgAnnotatedVariable) var;
		assertEquals("var_y", avar.getName());
		assertTrue(avar.getType() instanceof PGoTypeString);
		assertFalse(avar.isPositionalArg());
		assertEquals("argname", avar.getArgName());

		try {
			parts = new String[] { "arg", "x", "int", "argname", "extra" };
			AnnotatedVariable.parse(2, parts, generator);
			fail("Exception expected for extra argument");
		} catch (PGoParseException e) {

		}

		try {
			parts = new String[] { "arg", "x" };
			AnnotatedVariable.parse(2, parts, generator);
			fail("Exception expected for missing argument");
		} catch (PGoParseException e) {

		}

		try {
			parts = new String[] { "arg", "x", "wrongtype" };
			AnnotatedVariable.parse(2, parts, generator);
			fail("Exception expected for unknown type");
		} catch (PGoTransException e) {

		}
	}

	@Test
	public void testVars() throws PGoParseException, PGoTransException {
		String[] parts;
		AnnotatedVariable var;
		VarAnnotatedVariable vvar;

		parts = new String[] { "var", "x", "int" };
		var = AnnotatedVariable.parse(0, parts, generator);
		assertTrue(var instanceof VarAnnotatedVariable);
		assertEquals(0, var.getLine());
		vvar = (VarAnnotatedVariable) var;
		assertEquals("x", vvar.getName());
		assertTrue(vvar.getType() instanceof PGoTypeInt);

		parts = new String[] { "var", "var_y", "string" };
		var = AnnotatedVariable.parse(2, parts, generator);
		assertTrue(var instanceof VarAnnotatedVariable);
		assertEquals(2, var.getLine());
		vvar = (VarAnnotatedVariable) var;
		assertEquals("var_y", vvar.getName());
		assertTrue(vvar.getType() instanceof PGoTypeString);

		try {
			parts = new String[] { "var", "x", "int", "extra" };
			AnnotatedVariable.parse(2, parts, generator);
			fail("Exception expected for extra argument");
		} catch (PGoParseException e) {

		}

		try {
			parts = new String[] { "var", "x" };
			AnnotatedVariable.parse(2, parts, generator);
			fail("Exception expected for missing argument");
		} catch (PGoParseException e) {

		}

		try {
			parts = new String[] { "var", "x", "wrongtype" };
			AnnotatedVariable.parse(2, parts, generator);
			fail("Exception expected for unknown type");
		} catch (PGoTransException e) {

		}
	}

	@Test
	public void testFillVariable() throws PGoParseException, PGoTransException {
		PGoVariable v;
		AnnotatedVariable av;

		v = PGoVariable.convert("var", generator.get());
		av = AnnotatedVariable.parse(2, new String[] { "const", "var", "int", "50" }, generator);
		av.applyAnnotationOnVariable(v);
		assertTrue(v.getIsConstant());
		assertEquals(PGoTypeInt.getInstance(), v.getType());
		assertTrue(v.getIsSimpleAssignInit());
		assertEquals("50", v.getGoVal());
		assertNull(v.getArgInfo());

		v = PGoVariable.convert("var", generator.get());
		av = AnnotatedVariable.parse(2, new String[] { "arg", "var", "int" }, generator);
		av.applyAnnotationOnVariable(v);
		assertFalse(v.getIsConstant());
		assertEquals(PGoTypeInt.getInstance(), v.getType());
		assertTrue(v.getIsSimpleAssignInit());
		assertEquals(av, v.getArgInfo());

		v = PGoVariable.convert("var", generator.get());
		av = AnnotatedVariable.parse(2, new String[] { "arg", "var", "int", "varflag" }, generator);
		av.applyAnnotationOnVariable(v);
		assertFalse(v.getIsConstant());
		assertEquals(PGoTypeInt.getInstance(), v.getType());
		assertTrue(v.getIsSimpleAssignInit());
		assertEquals(av, v.getArgInfo());

		v = PGoVariable.convert("var", generator.get());
		av = AnnotatedVariable.parse(2, new String[] { "var", "var", "string" }, generator);
		av.applyAnnotationOnVariable(v);
		assertFalse(v.getIsConstant());
		assertEquals(PGoTypeString.getInstance(), v.getType());
		assertNull(v.getArgInfo());
	}
}
