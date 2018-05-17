package pgo.parser;

import org.junit.Test;
import pgo.model.parser.*;
import pgo.model.parser.AnnotatedVariable.ArgAnnotatedVariable;
import pgo.model.parser.AnnotatedVariable.ConstAnnotatedVariable;
import pgo.model.parser.AnnotatedVariable.VarAnnotatedVariable;
import pgo.model.type.*;
import pgo.trans.PGoTransException;

import java.util.Vector;

import static org.junit.Assert.*;

public class PGoAnnotationParserTest {
	private static PGoTypeGenerator generator = new PGoTypeGenerator("test");

	@Test
	public void testAnnotationParser() throws PGoParseException, PGoTransException {
		Vector<PGoAnnotation> annots = new Vector<>();
		annots.add(new PGoAnnotation("const cvar int 2", 4));
		annots.add(new PGoAnnotation("arg N int numT", 5));
		annots.add(new PGoAnnotation("var s string", 10));
		annots.add(new PGoAnnotation("func int foo() int", 21));
		annots.add(new PGoAnnotation("func bar() map[string]int", 25));
		annots.add(new PGoAnnotation("ret ret", 6));
		annots.add(new PGoAnnotation("ret fRet", 50));
		annots.add(new PGoAnnotation("proc int Client", 100));
		annots.add(new PGoAnnotation("proc string Server", 150));
		annots.add(new PGoAnnotation("lock true", 200));

		PGoAnnotationParser parser = new PGoAnnotationParser(annots, generator);

		assertEquals(3, parser.getAnnotatedVariables().size());
		assertTrue(parser.getAnnotatedVariable("cvar") instanceof ConstAnnotatedVariable);
		ConstAnnotatedVariable cv = (ConstAnnotatedVariable) parser.getAnnotatedVariable("cvar");
		assertNotNull(cv);
		assertEquals(4, cv.getLine());
		assertEquals("cvar", cv.getName());
		assertEquals("2", cv.getVal());
		assertTrue(cv.getType() instanceof PGoTypeInt);

		assertTrue(parser.getAnnotatedVariable("N") instanceof ArgAnnotatedVariable);
		ArgAnnotatedVariable av = (ArgAnnotatedVariable) parser.getAnnotatedVariable("N");
		assertNotNull(av);
		assertEquals(5, av.getLine());
		assertEquals("N", av.getName());
		assertEquals("numT", av.getArgName());
		assertTrue(av.getType() instanceof PGoTypeInt);

		assertTrue(parser.getAnnotatedVariable("s") instanceof VarAnnotatedVariable);
		VarAnnotatedVariable vv = (VarAnnotatedVariable) parser.getAnnotatedVariable("s");
		assertNotNull(vv);
		assertEquals(10, vv.getLine());
		assertEquals("s", vv.getName());
		assertTrue(vv.getType() instanceof PGoTypeString);

		assertEquals(2, parser.getAnnotatedFunctions().size());
		AnnotatedFunction f = parser.getAnnotatedFunction("foo");
		assertNotNull(f);
		assertEquals("foo", f.getName());
		assertEquals(21, f.getLine());
		assertTrue(f.getReturnType() instanceof PGoTypeInt);
		assertEquals(1, f.getArgTypes().size());
		assertTrue(f.getArgTypes().get(0) instanceof PGoTypeInt);

		f = parser.getAnnotatedFunction("bar");
		assertNotNull(f);
		assertEquals("bar", f.getName());
		assertEquals(25, f.getLine());
		assertTrue(f.getReturnType() instanceof PGoTypeVoid);
		assertEquals(1, f.getArgTypes().size());
		assertTrue(f.getArgTypes().get(0) instanceof PGoTypeMap);

		assertEquals(2, parser.getReturnVariables().size());
		AnnotatedReturnVariable rv;
		rv = parser.getReturnVariable("ret");
		assertNotNull(rv);
		assertEquals("ret", rv.getName());
		assertEquals(6, rv.getLine());

		rv = parser.getReturnVariable("fRet");
		assertNotNull(rv);
		assertEquals("fRet", rv.getName());
		assertEquals(50, rv.getLine());

		assertEquals(2, parser.getAnnotatedProcesses().size());
		AnnotatedProcess pr = parser.getAnnotatedProcess("Client");
		assertNotNull(pr);
		assertEquals("Client", pr.getName());
		assertEquals(100, pr.getLine());
		assertTrue(pr.getIdType() instanceof PGoTypeInt);

		pr = parser.getAnnotatedProcess("Server");
		assertNotNull(pr);
		assertEquals("Server", pr.getName());
		assertEquals(150, pr.getLine());
		assertTrue(pr.getIdType() instanceof PGoTypeString);

		AnnotatedLock al = parser.getAnnotatedLock();
		assertTrue(al.needsLock());
		assertEquals(200, al.getLine());
	}

}
