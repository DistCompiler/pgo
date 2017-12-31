package pgo.model.intermediate;

import static junit.framework.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import pgo.model.intermediate.PGoPrimitiveType.PGoBool;
import pgo.model.intermediate.PGoPrimitiveType.PGoDecimal;
import pgo.model.intermediate.PGoPrimitiveType.PGoInt;
import pgo.model.intermediate.PGoPrimitiveType.PGoNatural;
import pgo.model.intermediate.PGoPrimitiveType.PGoString;
import pgo.model.intermediate.PGoPrimitiveType.PGoVoid;
import pgo.model.intermediate.PGoPrimitiveType.PGoTemplateArgument;
import pgo.model.intermediate.PGoType.PGoUndetermined;

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
		assertEquals(ptype, pt);
		assertEquals(PGoPrimitiveType.inferPrimitiveFromGoTypeName(pt.toTypeName()), pt);
	}

	@Parameterized.Parameters
	public static Collection testCases() {
		return Arrays.asList(new Object[][] { { "int", new PGoInt() }, { "integer", new PGoInt() },
				{ "float64", new PGoDecimal() }, { "decimal", new PGoDecimal() }, { "natural", new PGoNatural() },
				{ "uint64", new PGoNatural() }, { "bool", new PGoBool() }, { "boolean", new PGoBool() },
				{ "String", new PGoString() }, { "void", new PGoVoid() }, { "asf", new PGoUndetermined() },
				{ "E", new PGoTemplateArgument("e") }
				 });
	}
}
