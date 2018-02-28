package pgo.model.intermediate;

import static junit.framework.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import pgo.model.intermediate.PGoCollectionType.PGoChan;
import pgo.model.intermediate.PGoCollectionType.PGoMap;
import pgo.model.intermediate.PGoCollectionType.PGoSet;
import pgo.model.intermediate.PGoCollectionType.PGoSlice;
import pgo.model.intermediate.PGoCollectionType.PGoTuple;
import pgo.model.intermediate.PGoPrimitiveType.PGoBool;
import pgo.model.intermediate.PGoPrimitiveType.PGoDecimal;
import pgo.model.intermediate.PGoPrimitiveType.PGoInt;
import pgo.model.intermediate.PGoPrimitiveType.PGoString;
import pgo.model.intermediate.PGoType.PGoUndetermined;

public class PGoContainerTypeTest {

	@Test
	public void testSlice() {
		String s;
		PGoType pt;
		PGoSlice ps;

		s = "[]int";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSlice);
		ps = (PGoSlice) pt;
		assertTrue(ps.getElementType() instanceof PGoInt);
		assertEquals("", ps.getInitCap());
		assertEquals(s, ps.toTypeName());
		assertFalse(ps.isUndetermined());

		s = "[4]int";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSlice);
		ps = (PGoSlice) pt;
		assertTrue(ps.getElementType() instanceof PGoInt);
		assertEquals("4", ps.getInitCap());
		assertEquals(s, ps.toTypeName());
		assertFalse(ps.isUndetermined());

		s = "[][]bool";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSlice);
		ps = (PGoSlice) pt;
		assertTrue(ps.getElementType() instanceof PGoSlice);
		assertEquals("", ps.getInitCap());
		assertFalse(ps.isUndetermined());
		ps = (PGoSlice) ps.getElementType();
		assertEquals("", ps.getInitCap());
		assertFalse(ps.isUndetermined());
		assertTrue(ps.getElementType() instanceof PGoBool);
		assertEquals(s, pt.toTypeName());

		s = "[]map[int]bool";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSlice);
		ps = (PGoSlice) pt;
		assertFalse(ps.isUndetermined());
		assertTrue(ps.getElementType() instanceof PGoMap);
		assertEquals("", ps.getInitCap());
		assertEquals(s, pt.toTypeName());

		s = "[]asf";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);

		s = "[][]asf";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);
	}

	@Test
	public void testChan() {
		String s;
		PGoType pt;
		PGoChan pc;

		s = "chan[int]";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoChan);
		pc = (PGoChan) pt;
		assertFalse(pc.isUndetermined());
		assertTrue(pc.getElementType() instanceof PGoInt);
		assertEquals(s.toLowerCase(), pc.toTypeName().toLowerCase());

		s = "Chan[chan[bool]]";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoChan);
		pc = (PGoChan) pt;
		assertFalse(pc.isUndetermined());
		assertTrue(pc.getElementType() instanceof PGoChan);
		pc = (PGoChan) pc.getElementType();
		assertFalse(pc.isUndetermined());
		assertTrue(pc.getElementType() instanceof PGoBool);
		assertEquals(s.toLowerCase(), pt.toTypeName().toLowerCase());

		s = "chan[[]int]";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoChan);
		pc = (PGoChan) pt;
		assertFalse(pc.isUndetermined());
		assertTrue(pc.getElementType() instanceof PGoSlice);
		assertEquals(s.toLowerCase(), pt.toTypeName().toLowerCase());

		s = "chan[asf]";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);

		s = "chan[chan[asf]]";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);
	}
	
	@Test
	public void testSet() {
		String s;
		PGoType pt;
		PGoSet ps;

		s = "set[int]";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSet);
		ps = (PGoSet) pt;
		assertFalse(ps.isUndetermined());
		assertTrue(ps.getElementType() instanceof PGoInt);
		assertEquals(s.toLowerCase(), pt.toTypeName().toLowerCase());

		s = "set[set[bool]]";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSet);
		ps = (PGoSet) pt;
		assertFalse(ps.isUndetermined());
		assertTrue(ps.getElementType() instanceof PGoSet);
		ps = (PGoSet) ps.getElementType();
		assertFalse(ps.isUndetermined());
		assertTrue(ps.getElementType() instanceof PGoBool);
		assertEquals(s.toLowerCase(), pt.toTypeName().toLowerCase());

		s = "Set[[]int]";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSet);
		ps = (PGoSet) pt;
		assertFalse(ps.isUndetermined());
		assertTrue(ps.getElementType() instanceof PGoSlice);
		assertEquals(s.toLowerCase(), pt.toTypeName().toLowerCase());

		s = "set[asf]";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);

		s = "set[set[asf]]";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);
	}

	@Test
	public void testMap() {
		String s;
		PGoType pt;
		PGoMap pm;

		s = "map[int]bool";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoMap);
		pm = (PGoMap) pt;
		assertFalse(pm.isUndetermined());
		assertTrue(pm.getKeyType() instanceof PGoInt);
		assertTrue(pm.getElementType() instanceof PGoBool);
		assertEquals(s.toLowerCase(), pm.toTypeName().toLowerCase());

		s = "Map[int]map[int]bool";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoMap);
		pm = (PGoMap) pt;
		assertFalse(pm.isUndetermined());
		assertTrue(pm.getKeyType() instanceof PGoInt);
		assertTrue(pm.getElementType() instanceof PGoMap);
		pm = (PGoMap) pm.getElementType();
		assertFalse(pm.isUndetermined());
		assertTrue(pm.getKeyType() instanceof PGoInt);
		assertTrue(pm.getElementType() instanceof PGoBool);
		assertEquals(s.toLowerCase(), pt.toTypeName().toLowerCase());

		s = "map[String][]int";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoMap);
		pm = (PGoMap) pt;
		assertFalse(pm.isUndetermined());
		assertTrue(pm.getKeyType() instanceof PGoString);
		assertTrue(pm.getElementType() instanceof PGoSlice);
		assertEquals(s.toLowerCase(), pt.toTypeName().toLowerCase());

		s = "map[int]asf";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);

		s = "map[asf]int";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);

		s = "map[int]map[int]afs";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);
	}
	
	@Test
	public void testTuple() {
		String s = "tuple[int...]";
		PGoType type = PGoType.inferFromGoTypeName(s);
		assertTrue(type instanceof PGoTuple);
		PGoTuple tup = (PGoTuple) type;
		assertEquals(-1, tup.getLength());
		assertEquals(1, tup.getContainedTypes().size());
		assertTrue(tup.getContainedTypes().get(0) instanceof PGoInt);
		assertEquals(s, type.toTypeName());
		assertEquals("datatypes.Tuple", type.toGo());
		
		s = "tuple[int, map[int]string, tuple[string...], string]";
		type = PGoType.inferFromGoTypeName(s);
		assertTrue(type instanceof PGoTuple);
		tup = (PGoTuple) type;
		assertEquals(4, tup.getLength());
		assertTrue(tup.getType(0) instanceof PGoInt);
		assertTrue(tup.getType(1) instanceof PGoMap);
		assertTrue(tup.getType(2) instanceof PGoTuple);
		assertTrue(tup.getType(3) instanceof PGoString);
		assertEquals(s, type.toTypeName());
		assertEquals("datatypes.Tuple", type.toGo());
		
		s = "tuple[int, tuple[float64, string], []int]";
		type = PGoType.inferFromGoTypeName(s);
		assertTrue(type instanceof PGoTuple);
		tup = (PGoTuple) type;
		assertEquals(3, tup.getLength());
		assertTrue(tup.getType(0) instanceof PGoInt);
		assertTrue(tup.getType(1) instanceof PGoTuple);
		assertTrue(tup.getType(2) instanceof PGoSlice);
		PGoTuple innerTup = (PGoTuple) tup.getType(1);
		assertTrue(innerTup.getType(0) instanceof PGoDecimal);
		assertTrue(innerTup.getType(1) instanceof PGoString);
		assertEquals(s, type.toTypeName());
		assertEquals("datatypes.Tuple", type.toGo());
		
		s = "tuple[]";
		type = PGoType.inferFromGoTypeName(s);
		assertTrue(type instanceof PGoTuple);
		tup = (PGoTuple) type;
		assertEquals(0, tup.getLength());
		assertEquals(s, type.toTypeName());
		assertEquals("datatypes.Tuple", type.toGo());
	}
}
