package pgo.model.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.util.Vector;

import org.junit.Test;

import pcal.AST.Procedure;
import pcal.AST.Process;
import pcal.AST.VarDecl;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoVariable;
import pgo.model.type.PGoTypeGenerator;
import pgo.model.type.PGoTypeInt;
import pgo.parser.PGoParseException;
import pgo.trans.PGoTransException;

public class AnnotatedProcessTest {
	private static PGoTypeGenerator generator = new PGoTypeGenerator("test");

	@Test
	public void testFillFunction() throws PGoParseException, PGoTransException {
		PGoFunction f;
		AnnotatedProcess ap;
		VarDecl pv;

		Process p = new Process();
		p.decls = new Vector();
		p.name = "Proc";
		f = PGoFunction.convert(p, PGoFunction.FunctionKind.GoRoutine, generator);
		ap = AnnotatedProcess.parse(1, new String[] { "proc", "int", "Proc" }, generator);
		ap.applyAnnotationOnFunction(f);
		assertEquals(1, f.getParams().size());
		assertEquals(PGoTypeInt.getInstance(), f.getParam(PGoVariable.PROCESS_VAR_ARG).getType());

		Procedure pc = new Procedure();
		pc.decls = new Vector();
		pc.params = new Vector();
		pc.name = "Proc";
		f = PGoFunction.convert(pc, generator);
		try {
			ap.applyAnnotationOnFunction(f);
			fail("Exception expected for not a goroutine function");
		} catch (PGoTransException e) {

		}
	}
}
