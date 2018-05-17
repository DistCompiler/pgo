package pgo.model.intermediate;

import static org.junit.Assert.*;

import java.util.Arrays;
import java.util.Optional;
import java.util.Vector;

import org.junit.Test;
import pgo.model.type.*;
import pgo.model.type.PGoType;

public class PGoLibFunctionTest {
	private static PGoTypeGenerator generator = new PGoTypeGenerator("test");

	@Test
	public void testSimple() {
		PGoLibFunction lfunc = new PGoLibFunction("foo");
		Vector<PGoType> params = new Vector<>();
		params.add(PGoTypeString.getInstance());
		params.add(PGoTypeInt.getInstance());
		lfunc.addFuncSignature(params, "datatypes.Foo", false, PGoTypeVoid.getInstance());
		PGoLibFunction.LibFuncInfo fInfo = lfunc.getFunc(generator, params).get();
		assertEquals("datatypes.Foo", fInfo.getGoName());
		assertFalse(fInfo.isObjMethod());
		assertEquals(PGoTypeVoid.getInstance(), fInfo.getReturnType());
		
		params = new Vector<>();
		params.add(new PGoTypeSet(PGoTypeInt.getInstance()));
		params.add(PGoTypeInt.getInstance());
		lfunc.addFuncSignature(params, "datatypes.Bar", true, PGoTypeBool.getInstance());
		fInfo = lfunc.getFunc(generator, params).get();
		assertEquals("datatypes.Bar", fInfo.getGoName());
		assertTrue(fInfo.isObjMethod());
		assertEquals(PGoTypeBool.getInstance(), fInfo.getReturnType());
		
		params = new Vector<>();
		params.add(PGoTypeString.getInstance());
		params.add(PGoTypeInt.getInstance());
		fInfo = lfunc.getFunc(generator, params).get();
		assertEquals("datatypes.Foo", fInfo.getGoName());
		
		params = new Vector<>();
		assertEquals(Optional.empty(), lfunc.getFunc(generator, params));
	}
	
	@Test
	public void testWithGenerics() {
		PGoLibFunction lfunc = new PGoLibFunction("foo");
		Vector<PGoType> params = new Vector<>();
		PGoType fresh = generator.get();
		params.add(fresh);
		params.add(fresh);
		lfunc.addFuncSignature(params, "datatypes.Foo", false, fresh);
		
		params = new Vector<>();
		params.add(PGoTypeInt.getInstance());
		params.add(PGoTypeInt.getInstance());
		PGoLibFunction.LibFuncInfo fInfo = lfunc.getFunc(generator, params).get();
		assertEquals("datatypes.Foo", fInfo.getGoName());
		assertEquals(PGoTypeInt.getInstance(), fInfo.getReturnType().realize());
		
		params = new Vector<>();
		params.add(PGoTypeString.getInstance());
		params.add(PGoTypeString.getInstance());
		fInfo = lfunc.getFunc(generator, params).get();
		assertEquals("datatypes.Foo", fInfo.getGoName());
		assertEquals(PGoTypeString.getInstance(), fInfo.getReturnType());
		
		params = new Vector<>();
		PGoType a = generator.get();
		PGoType b = generator.get();
		params.add(new PGoTypeSet(a));
		params.add(new PGoTypeSlice(b));
		lfunc.addFuncSignature(params, "datatypes.Bar", true, new PGoTypeTuple(Arrays.asList(a, b)));
		
		params = new Vector<>();
		params.add(new PGoTypeSet(new PGoTypeSet(PGoTypeInt.getInstance())));
		params.add(new PGoTypeSlice(new PGoTypeMap(PGoTypeInt.getInstance(), PGoTypeString.getInstance())));
		fInfo = lfunc.getFunc(generator, params).get();
		assertEquals("datatypes.Bar", fInfo.getGoName());
		assertEquals(new PGoTypeTuple(Arrays.asList(new PGoTypeSet(PGoTypeInt.getInstance()), new PGoTypeMap(PGoTypeInt.getInstance(), PGoTypeString.getInstance()))), fInfo.getReturnType().realize());
		
		params = new Vector<>();
		params.add(new PGoTypeSet(PGoTypeDecimal.getInstance()));
		params.add(new PGoTypeSlice(PGoTypeString.getInstance()));
		params.add(PGoTypeInt.getInstance());
		assertEquals(Optional.empty(), lfunc.getFunc(generator, params));
	}
}
