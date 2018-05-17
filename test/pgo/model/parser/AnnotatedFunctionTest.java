package pgo.model.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import org.junit.Test;

import pcal.AST.PVarDecl;
import pcal.AST.Procedure;
import pgo.model.intermediate.PGoFunction;
import pgo.model.type.*;
import pgo.parser.PGoParseException;
import pgo.trans.PGoTransException;

public class AnnotatedFunctionTest {
	private static PGoTypeGenerator generator = new PGoTypeGenerator("test");

	@Test
	public void testVoidFunction() throws PGoParseException, PGoTransException {
		String[] parts;
		AnnotatedFunction fun;
		Vector<PGoType> argTypes ;

		parts = new String[] { "func", "fun()" };
		fun = AnnotatedFunction.parse(0, parts, generator);
		assertEquals(0, fun.getLine());
		assertEquals("fun", fun.getName());
		assertTrue(fun.getReturnType() instanceof PGoTypeVoid);
		argTypes = fun.getArgTypes();
		assertEquals(0, argTypes.size());


		parts = new String[] { "func", "foo()", "int", "string" };
		fun = AnnotatedFunction.parse(2, parts, generator);
		assertEquals(2, fun.getLine());
		assertEquals("foo", fun.getName());
		assertTrue(fun.getReturnType() instanceof PGoTypeVoid);
		argTypes = fun.getArgTypes();
		assertEquals(2, argTypes.size());
		assertTrue(argTypes.get(0) instanceof PGoTypeInt);
		assertTrue(argTypes.get(1) instanceof PGoTypeString);

		try {
			parts = new String[] { "func", "foo()", "wrongtype", "string" };
			AnnotatedFunction.parse(2, parts, generator);
			fail("Exception expected for unknown type");
		} catch (PGoTransException e) {

		}
	}

	@Test
	public void testReturnFunction() throws PGoParseException, PGoTransException {
		String[] parts;
		AnnotatedFunction fun;
		Vector<PGoType> argTypes;

		parts = new String[] { "func", "int", "fun()" };
		fun = AnnotatedFunction.parse(0, parts, generator);
		assertEquals(0, fun.getLine());
		assertEquals("fun", fun.getName());
		assertTrue(fun.getReturnType() instanceof PGoTypeInt);
		argTypes = fun.getArgTypes();
		assertEquals(0, argTypes.size());

		parts = new String[] { "func", "bool", "foo()", "int", "string" };
		fun = AnnotatedFunction.parse(2, parts, generator);
		assertEquals(2, fun.getLine());
		assertEquals("foo", fun.getName());
		assertTrue(fun.getReturnType() instanceof PGoTypeBool);
		argTypes = fun.getArgTypes();
		assertEquals(2, argTypes.size());
		assertTrue(argTypes.get(0) instanceof PGoTypeInt);
		assertTrue(argTypes.get(1) instanceof PGoTypeString);

		try {
			parts = new String[] { "func", "bool", "foo()", "wrongtype", "string" };
			AnnotatedFunction.parse(2, parts, generator);
			fail("Exception expected for unknown type");
		} catch (PGoTransException e) {

		}

		try {
			parts = new String[] { "func", "unknowntype", "foo()", "int", "string" };
			AnnotatedFunction.parse(2, parts, generator);
			fail("Exception expected for unknown type");
		} catch (PGoTransException e) {

		}
	}

	@Test
	public void testFillFunction() throws PGoParseException, PGoTransException {
		PGoFunction f;
		AnnotatedFunction af;
		Procedure p;
		PVarDecl pv;
		List<AnnotatedReturnVariable> rvs = new ArrayList<>();

		p = new Procedure();
		p.params = new Vector();
		p.decls = new Vector();
		p.name = "func";
		f = PGoFunction.convert(p, generator);
		af = AnnotatedFunction.parse(1, new String[] { "func", "func()" }, generator);
		af.applyAnnotationOnFunction(f, rvs);
		assertEquals(0, f.getParams().size());
		assertEquals(PGoTypeVoid.getInstance(), f.getReturnType());

		pv = new PVarDecl();
		pv.var = "Param1";
		p.params.add(pv);
		f = PGoFunction.convert(p, generator);
		try {
			af.applyAnnotationOnFunction(f, rvs);
			fail("Exception expected for parameter size mismatch");
		} catch (PGoTransException e) {

		}

		af = AnnotatedFunction.parse(2, new String[] { "func", "void", "func()", "int" }, generator);
		af.applyAnnotationOnFunction(f, rvs);
		assertEquals(1, f.getParams().size());
		assertEquals(PGoTypeInt.getInstance(), f.getParam("Param1").getType());
		assertEquals(PGoTypeVoid.getInstance(), f.getReturnType());

		pv = new PVarDecl();
		pv.var = "Param2";
		p.params.add(pv);
		f = PGoFunction.convert(p, generator);

		af = AnnotatedFunction.parse(2, new String[] { "func", "boolean", "func()", "int", "string" }, generator);
		af.applyAnnotationOnFunction(f, rvs);
		assertEquals(2, f.getParams().size());
		assertEquals(PGoTypeInt.getInstance(), f.getParam("Param1").getType());
		assertEquals(PGoTypeString.getInstance(), f.getParam("Param2").getType());
		assertEquals(PGoTypeBool.getInstance(), f.getReturnType());

		rvs.add(AnnotatedReturnVariable.parse(2, new String[] {"ret", "ret"}));
		pv = new PVarDecl();
		pv.var = "ret";
		p.decls.add(pv);
		f = PGoFunction.convert(p, generator);
		af.applyAnnotationOnFunction(f, rvs);
		assertEquals(2, f.getParams().size());
		assertEquals(PGoTypeInt.getInstance(), f.getParam("Param1").getType());
		assertEquals(PGoTypeString.getInstance(), f.getParam("Param2").getType());
		assertEquals(PGoTypeBool.getInstance(), f.getReturnType());
		assertEquals(PGoTypeBool.getInstance(), f.getVariable("ret").getType());
	}
}
