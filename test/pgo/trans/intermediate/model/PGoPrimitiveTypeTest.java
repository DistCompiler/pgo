package pgo.trans.intermediate.model;

import static junit.framework.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import pgo.trans.intermediate.model.PGoPrimitiveType.PGoBool;
import pgo.trans.intermediate.model.PGoPrimitiveType.PGoDecimal;
import pgo.trans.intermediate.model.PGoPrimitiveType.PGoInt;
import pgo.trans.intermediate.model.PGoPrimitiveType.PGoNatural;
import pgo.trans.intermediate.model.PGoPrimitiveType.PGoString;
import pgo.trans.intermediate.model.PGoPrimitiveType.PGoVoid;
import pgo.trans.intermediate.model.PGoType.PGoUndetermined;

@RunWith(Parameterized.class)
public class PGoPrimitiveTypeTest {

	private String typename;
	private PGoType ptype;

	public PGoPrimitiveTypeTest(String tn, PGoType pt) {
		typename = tn;
		ptype = pt;
	}

	@Test
	public void testConvertTypeName() {
		PGoType pt = PGoPrimitiveType.inferPrimitiveFromGoTypeName(typename);
		assertEquals(ptype.getClass(), pt.getClass());
		assertEquals(PGoPrimitiveType.inferPrimitiveFromGoTypeName(pt.toGoTypeName()).getClass(), pt.getClass());
	}

	@Parameterized.Parameters
	public static Collection primeNumbers() {
		return Arrays.asList(new Object[][] { { "int", new PGoInt() }, { "integer", new PGoInt() },
				{ "float64", new PGoDecimal() }, { "decimal", new PGoDecimal() }, { "natural", new PGoNatural() },
				{ "uint64", new PGoNatural() }, { "bool", new PGoBool() }, { "boolean", new PGoBool() },
				{ "String", new PGoString() }, { "void", new PGoVoid() }, { "asf", new PGoUndetermined() }
				 });
	}
}
