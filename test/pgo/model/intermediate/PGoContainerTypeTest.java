package pgo.model.intermediate;

import static junit.framework.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import pgo.model.intermediate.PGoContainerType.PGoChan;
import pgo.model.intermediate.PGoContainerType.PGoMap;
import pgo.model.intermediate.PGoContainerType.PGoSet;
import pgo.model.intermediate.PGoContainerType.PGoSlice;
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
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSlice);
		ps = (PGoSlice) pt;
		assertTrue(ps.getElementType() instanceof PGoInt);
		assertEquals("", ps.getInitCap());
		assertEquals(s, ps.toGoTypeName());
		assertFalse(ps.isUndetermined());

		s = "[4]int";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSlice);
		ps = (PGoSlice) pt;
		assertTrue(ps.getElementType() instanceof PGoInt);
		assertEquals("4", ps.getInitCap());
		assertEquals(s, ps.toGoTypeName());
		assertFalse(ps.isUndetermined());

		s = "[][]bool";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSlice);
		ps = (PGoSlice) pt;
		assertTrue(ps.getElementType() instanceof PGoSlice);
		assertEquals("", ps.getInitCap());
		assertFalse(ps.isUndetermined());
		ps = (PGoSlice) ps.getElementType();
		assertEquals("", ps.getInitCap());
		assertFalse(ps.isUndetermined());
		assertTrue(ps.getElementType() instanceof PGoBool);
		assertEquals(s, pt.toGoTypeName());

		s = "[]map[int]bool";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSlice);
		ps = (PGoSlice) pt;
		assertFalse(ps.isUndetermined());
		assertTrue(ps.getElementType() instanceof PGoMap);
		assertEquals("", ps.getInitCap());
		assertEquals(s, pt.toGoTypeName());

		s = "[]a";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);

		s = "[][]a";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);
	}

	@Test
	public void testChan() {
		String s;
		PGoType pt;
		PGoChan pc;

		s = "chan int";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoChan);
		pc = (PGoChan) pt;
		assertFalse(pc.isUndetermined());
		assertTrue(pc.getElementType() instanceof PGoInt);
		assertEquals(s, pc.toGoTypeName());

		s = "chan chan bool";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoChan);
		pc = (PGoChan) pt;
		assertFalse(pc.isUndetermined());
		assertTrue(pc.getElementType() instanceof PGoChan);
		pc = (PGoChan) pc.getElementType();
		assertFalse(pc.isUndetermined());
		assertTrue(pc.getElementType() instanceof PGoBool);
		assertEquals(s, pt.toGoTypeName());

		s = "chan []int";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoChan);
		pc = (PGoChan) pt;
		assertFalse(pc.isUndetermined());
		assertTrue(pc.getElementType() instanceof PGoSlice);
		assertEquals(s, pt.toGoTypeName());

		s = "chan a";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);

		s = "chan chan a";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);
	}
	
	@Test
	public void testSet() {
		String s;
		PGoType pt;
		PGoSet ps;

		s = "set[]int";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSet);
		ps = (PGoSet) pt;
		assertFalse(ps.isUndetermined());
		assertTrue(ps.getElementType() instanceof PGoInt);
		assertEquals(s, ps.toGoTypeName());

		s = "set[]set[]bool";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSet);
		ps = (PGoSet) pt;
		assertFalse(ps.isUndetermined());
		assertTrue(ps.getElementType() instanceof PGoSet);
		ps = (PGoSet) ps.getElementType();
		assertFalse(ps.isUndetermined());
		assertTrue(ps.getElementType() instanceof PGoBool);
		assertEquals(s, pt.toGoTypeName());

		s = "set[][]int";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSet);
		ps = (PGoSet) pt;
		assertFalse(ps.isUndetermined());
		assertTrue(ps.getElementType() instanceof PGoSlice);
		assertEquals(s, pt.toGoTypeName());

		s = "set[]a";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);

		s = "set[]set[]a";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);
	}

	@Test
	public void testMap() {
		String s;
		PGoType pt;
		PGoMap pm;

		s = "map[int]bool";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoMap);
		pm = (PGoMap) pt;
		assertFalse(pm.isUndetermined());
		assertTrue(pm.getKeyType() instanceof PGoInt);
		assertTrue(pm.getElementType() instanceof PGoBool);
		assertEquals(s, pm.toGoTypeName());

		s = "map[int]map[int]bool";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoMap);
		pm = (PGoMap) pt;
		assertFalse(pm.isUndetermined());
		assertTrue(pm.getKeyType() instanceof PGoInt);
		assertTrue(pm.getElementType() instanceof PGoMap);
		pm = (PGoMap) pm.getElementType();
		assertFalse(pm.isUndetermined());
		assertTrue(pm.getKeyType() instanceof PGoInt);
		assertTrue(pm.getElementType() instanceof PGoBool);
		assertEquals(s, pt.toGoTypeName());

		s = "map[String][]int";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoMap);
		pm = (PGoMap) pt;
		assertFalse(pm.isUndetermined());
		assertTrue(pm.getKeyType() instanceof PGoString);
		assertTrue(pm.getElementType() instanceof PGoSlice);
		assertEquals(s, pt.toGoTypeName());

		s = "map[int]a";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);

		s = "map[a]int";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);

		s = "map[int]map[int]a";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoUndetermined);
	}
}
