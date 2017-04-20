package pgo.model.intermediate;

import static junit.framework.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import pgo.model.intermediate.PGoCollectionType.PGoChan;
import pgo.model.intermediate.PGoCollectionType.PGoMap;
import pgo.model.intermediate.PGoCollectionType.PGoSet;
import pgo.model.intermediate.PGoCollectionType.PGoSlice;
import pgo.model.intermediate.PGoPrimitiveType.PGoBool;
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

		s = "[]a";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);

		s = "[][]a";
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

		s = "chan[a]";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);

		s = "chan[chan[a]]";
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

		s = "set[a]";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);

		s = "set[set[a]]";
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

		s = "map[int]a";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);

		s = "map[a]int";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);

		s = "map[int]map[int]a";
		pt = PGoCollectionType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);
	}
}
