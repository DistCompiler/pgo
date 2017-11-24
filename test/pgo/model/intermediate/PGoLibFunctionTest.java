package pgo.model.intermediate;

import static org.junit.Assert.*;

import java.util.Vector;

import org.junit.Test;

public class PGoLibFunctionTest {
	
	@Test
	public void testSimple() {
		PGoLibFunction lfunc = new PGoLibFunction("foo");
		Vector<PGoType> params = new Vector<>();
		params.add(PGoType.inferFromGoTypeName("string"));
		params.add(PGoType.inferFromGoTypeName("int"));
		lfunc.addFuncSignature(params, "pgoutil.Foo", false, PGoPrimitiveType.VOID);
		assertEquals("pgoutil.Foo", lfunc.getGoName(params));
		assertEquals(false, lfunc.isObjectMethod(params));
		assertEquals(PGoPrimitiveType.VOID, lfunc.getRetType(params));
		
		params = new Vector<>();
		params.add(PGoType.inferFromGoTypeName("set[int]"));
		params.add(PGoType.inferFromGoTypeName("int"));
		lfunc.addFuncSignature(params, "pgoutil.Bar", true, PGoType.inferFromGoTypeName("bool"));
		assertEquals("pgoutil.Bar", lfunc.getGoName(params));
		assertEquals(true, lfunc.isObjectMethod(params));
		assertEquals(PGoType.inferFromGoTypeName("bool"), lfunc.getRetType(params));
		
		params = new Vector<>();
		params.add(PGoType.inferFromGoTypeName("string"));
		params.add(PGoType.inferFromGoTypeName("int"));
		assertEquals("pgoutil.Foo", lfunc.getGoName(params));
		
		params = new Vector<>();
		assertNull(lfunc.getGoName(params));
	}
	
	@Test
	public void testWithGenerics() {
		PGoLibFunction lfunc = new PGoLibFunction("foo");
		Vector<PGoType> params = new Vector<>();
		params.add(PGoType.inferFromGoTypeName("E"));
		params.add(PGoType.inferFromGoTypeName("E"));
		lfunc.addFuncSignature(params, "pgoutil.Foo", false, PGoType.inferFromGoTypeName("E"));
		
		params = new Vector<>();
		params.add(PGoType.inferFromGoTypeName("int"));
		params.add(PGoType.inferFromGoTypeName("int"));
		assertEquals("pgoutil.Foo", lfunc.getGoName(params));
		assertEquals(PGoType.inferFromGoTypeName("int"), lfunc.getRetType(params));
		
		params = new Vector<>();
		params.add(PGoType.inferFromGoTypeName("string"));
		params.add(PGoType.inferFromGoTypeName("string"));
		assertEquals("pgoutil.Foo", lfunc.getGoName(params));
		assertEquals(PGoType.inferFromGoTypeName("string"), lfunc.getRetType(params));
		
		params = new Vector<>();
		params.add(PGoType.inferFromGoTypeName("set[A]"));
		params.add(PGoType.inferFromGoTypeName("[]B"));
		lfunc.addFuncSignature(params, "pgoutil.Bar", true, PGoType.inferFromGoTypeName("tuple[A, B]"));
		
		params = new Vector<>();
		params.add(PGoType.inferFromGoTypeName("set[set[int]]"));
		params.add(PGoType.inferFromGoTypeName("[]map[int]string"));
		assertEquals("pgoutil.Bar", lfunc.getGoName(params));
		assertEquals(PGoType.inferFromGoTypeName("tuple[set[int], map[int]string]"), lfunc.getRetType(params));
		
		params = new Vector<>();
		params.add(PGoType.inferFromGoTypeName("set[float64]"));
		params.add(PGoType.inferFromGoTypeName("[]string"));
		params.add(PGoType.inferFromGoTypeName("int"));
		assertNull(lfunc.getGoName(params));
	}
}
