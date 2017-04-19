package pgo.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.Vector;

import org.junit.Test;

import pgo.model.intermediate.PGoContainerType.PGoMap;
import pgo.model.intermediate.PGoPrimitiveType.PGoInt;
import pgo.model.intermediate.PGoPrimitiveType.PGoString;
import pgo.model.intermediate.PGoPrimitiveType.PGoVoid;
import pgo.model.parser.AnnotatedFunction;
import pgo.model.parser.AnnotatedProcess;
import pgo.model.parser.AnnotatedReturnVariable;
import pgo.model.parser.AnnotatedVariable.ArgAnnotatedVariable;
import pgo.model.parser.AnnotatedVariable.ConstAnnotatedVariable;
import pgo.model.parser.AnnotatedVariable.VarAnnotatedVariable;
import pgo.model.parser.PGoAnnotation;

public class PGoAnnotationParserTest {

	@Test
	public void testAnnotationParser() throws PGoParseException {
		Vector<PGoAnnotation> annots = new Vector<PGoAnnotation>();
		annots.add(new PGoAnnotation("const int cvar 2",4));
		annots.add(new PGoAnnotation("arg int N numT", 5));
		annots.add(new PGoAnnotation("var string s", 10));
		annots.add(new PGoAnnotation("func int foo() int", 21));
		annots.add(new PGoAnnotation("func bar() map[string]int", 25));
		annots.add(new PGoAnnotation("ret ret", 6));
		annots.add(new PGoAnnotation("ret fRet", 50));
		annots.add(new PGoAnnotation("proc Client int", 100));
		annots.add(new PGoAnnotation("proc Server string", 150));

		PGoAnnotationParser parser = new PGoAnnotationParser(annots);

		assertEquals(3, parser.getAnnotatedVariables().size());
		assertTrue(parser.getAnnotatedVariable("cvar") instanceof ConstAnnotatedVariable);
		ConstAnnotatedVariable cv = (ConstAnnotatedVariable) parser.getAnnotatedVariable("cvar");
		assertNotNull(cv);
		assertEquals(4, cv.getLine());
		assertEquals("cvar", cv.getName());
		assertEquals("2",cv.getVal());
		assertTrue(cv.getType() instanceof PGoInt);
		
		assertTrue(parser.getAnnotatedVariable("N") instanceof ArgAnnotatedVariable);
		ArgAnnotatedVariable av = (ArgAnnotatedVariable) parser.getAnnotatedVariable("N");
		assertNotNull(av);
		assertEquals(5, av.getLine());
		assertEquals("N", av.getName());
		assertEquals("numT", av.getArgName());
		assertTrue(av.getType() instanceof PGoInt);
		
		assertTrue(parser.getAnnotatedVariable("s") instanceof VarAnnotatedVariable);
		VarAnnotatedVariable vv = (VarAnnotatedVariable) parser.getAnnotatedVariable("s");
		assertNotNull(vv);
		assertEquals(10, vv.getLine());
		assertEquals("s", vv.getName());
		assertTrue(vv.getType() instanceof PGoString);
		
		assertEquals(2, parser.getAnnotatedFunctions().size());
		AnnotatedFunction f = parser.getAnnotatedFunction("foo");
		assertNotNull(f);
		assertEquals("foo", f.getName());
		assertEquals(21, f.getLine());
		assertTrue(f.getReturnType() instanceof PGoInt);
		assertEquals(1,f.getArgTypes().size());
		assertTrue(f.getArgTypes().get(0) instanceof PGoInt);

		f = parser.getAnnotatedFunction("bar");
		assertNotNull(f);
		assertEquals("bar", f.getName());
		assertEquals(25, f.getLine());
		assertTrue(f.getReturnType() instanceof PGoVoid);
		assertEquals(1, f.getArgTypes().size());
		assertTrue(f.getArgTypes().get(0) instanceof PGoMap);
		
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
		assertTrue(pr.getIdType() instanceof PGoInt);

		pr = parser.getAnnotatedProcess("Server");
		assertNotNull(pr);
		assertEquals("Server", pr.getName());
		assertEquals(150, pr.getLine());
		assertTrue(pr.getIdType() instanceof PGoString);
	}

}
