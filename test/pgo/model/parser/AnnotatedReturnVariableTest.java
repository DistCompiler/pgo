package pgo.model.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.Vector;

import org.junit.Before;
import org.junit.Test;

import pcal.AST.Lhs;
import pcal.AST.PVarDecl;
import pcal.AST.Procedure;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoVariable;
import pgo.parser.PGoParseException;
import pgo.trans.PGoTransException;

public class AnnotatedReturnVariableTest {

	private LinkedHashMap<String, PGoVariable> globals;
	private ArrayList<PGoFunction> funcs;

	@Before
	public void SetUp() {
		globals = new LinkedHashMap<String, PGoVariable>();
		funcs = new ArrayList<PGoFunction>();

		for (int i = 0; i < 10; i++) {
			globals.put("var" + i, PGoVariable.convert(generator, "var" + i));
			Procedure p = new Procedure();
			p.params = new Vector();
			p.decls = new Vector();
			p.body = new Vector();
			p.name = "func" + i;

			funcs.add(PGoFunction.convert(p));
		}
		for (int i = 0; i < 10; i++) {
			Procedure p = new Procedure();
			p.params = new Vector();
			p.name = "OtherFunc" + i;
			p.decls = new Vector();
			p.body = new Vector();
			PVarDecl pv = new PVarDecl();
			pv.var = "OtherVar" + i;
			p.decls.add(pv);
			funcs.add(PGoFunction.convert(p));
		}
	}

	@Test
	public void testFixUpNoReference() throws PGoParseException, PGoTransException {
		PGoVariable v;

		AnnotatedReturnVariable.parse(new String[] { "ret", "var2" }, 2).applyAnnotation(globals, funcs);
		assertNull(globals.get("var2"));
		for (int i = 0; i < 10; i++) {
			if (i != 2) {
				assertNotNull(globals.get("var" + i));
			}
		}
		v = funcs.get(2).getVariable("var2");
		assertNull(v);
	}

	@Test
	public void testFixUpReference() throws PGoParseException, PGoTransException {
		PGoVariable v;

		Lhs ast = new Lhs();
		ast.var = "var2";
		funcs.get(2).getBody().add(ast);
		funcs.get(2).setReturnType(new PGoPrimitiveType.PGoBool());

		AnnotatedReturnVariable.parse(new String[] { "ret", "var2" }, 2).applyAnnotation(globals, funcs);
		assertNull(globals.get("var2"));
		for (int i = 0; i < 10; i++) {
			if (i != 2) {
				assertNotNull(globals.get("var" + i));
			}
		}
		v = funcs.get(2).getVariable("var2");
		assertNotNull(v);
		assertEquals(new PGoPrimitiveType.PGoBool(), v.getType());
	}

	@Test
	public void testFixUpExisting() throws PGoParseException, PGoTransException {
		PGoVariable v;

		funcs.get(12).setReturnType(new PGoPrimitiveType.PGoBool());

		AnnotatedReturnVariable.parse(new String[] { "ret", "OtherVar2" }, 2).applyAnnotation(globals, funcs);
		assertNull(globals.get("OtherVar2"));
		for (int i = 0; i < 10; i++) {
			assertNotNull(globals.get("var" + i));
		}
		v = funcs.get(12).getVariable("OtherVar2");
		assertNotNull(v);
		assertEquals(new PGoPrimitiveType.PGoBool(), v.getType());
	}

}
