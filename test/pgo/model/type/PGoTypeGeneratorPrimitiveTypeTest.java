package pgo.model.type;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import pgo.trans.PGoTransException;

import java.util.Arrays;
import java.util.Collection;

import static org.junit.Assert.*;

@RunWith(Parameterized.class)
public class PGoTypeGeneratorPrimitiveTypeTest {
	private String typename;
	private PGoType ptype;
	private PGoTypeGenerator generator = new PGoTypeGenerator("test");

	public PGoTypeGeneratorPrimitiveTypeTest(String tn, PGoType pt) {
		typename = tn;
		ptype = pt;
	}

	@Test
	public void testConvertTypeName() throws PGoTransException {
		PGoType pt = generator.inferFrom(typename);
		assertEquals(ptype, pt);
		assertEquals(generator.inferFrom(pt.toTypeName()), pt);
	}

	@Parameterized.Parameters
	public static Collection testCases() {
		return Arrays.asList(new Object[][] {
				{ "int", PGoTypeInt.getInstance() },
				{ "integer", PGoTypeInt.getInstance() },
				{ "float64", PGoTypeDecimal.getInstance() },
				{ "decimal", PGoTypeDecimal.getInstance() },
				{ "natural", PGoTypeNatural.getInstance() },
				{ "uint64", PGoTypeNatural.getInstance() },
				{ "bool", PGoTypeBool.getInstance() },
				{ "boolean", PGoTypeBool.getInstance() },
				{ "String", PGoTypeString.getInstance() },
				{ "void", PGoTypeVoid.getInstance() },
		});
	}
}
