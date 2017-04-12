package pgo.trans.intermediate.model;

import static junit.framework.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import pgo.trans.intermediate.model.PGoContainerType.PGoChan;
import pgo.trans.intermediate.model.PGoContainerType.PGoMap;
import pgo.trans.intermediate.model.PGoContainerType.PGoSet;
import pgo.trans.intermediate.model.PGoContainerType.PGoSlice;
import pgo.trans.intermediate.model.PGoPrimitiveType.PGoBool;
import pgo.trans.intermediate.model.PGoPrimitiveType.PGoInt;
import pgo.trans.intermediate.model.PGoPrimitiveType.PGoString;

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
		assertEquals(-1, ps.getInitCap());
		assertEquals(s, ps.toGoTypeName());

		s = "[4]int";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSlice);
		ps = (PGoSlice) pt;
		assertTrue(ps.getElementType() instanceof PGoInt);
		assertEquals(4, ps.getInitCap());
		assertEquals(s, ps.toGoTypeName());

		s = "[][]bool";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSlice);
		ps = (PGoSlice) pt;
		assertTrue(ps.getElementType() instanceof PGoSlice);
		assertEquals(-1, ps.getInitCap());
		ps = (PGoSlice) ps.getElementType();
		assertEquals(-1, ps.getInitCap());
		assertTrue(ps.getElementType() instanceof PGoBool);
		assertEquals(s, pt.toGoTypeName());

		s = "[]map[int]bool";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSlice);
		ps = (PGoSlice) pt;
		assertTrue(ps.getElementType() instanceof PGoMap);
		assertEquals(-1, ps.getInitCap());
		assertEquals(s, pt.toGoTypeName());
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
		assertTrue(pc.getElementType() instanceof PGoInt);
		assertEquals(s, pc.toGoTypeName());

		s = "chan chan bool";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSlice);
		pc = (PGoChan) pt;
		assertTrue(pc.getElementType() instanceof PGoChan);
		pc = (PGoChan) pc.getElementType();
		assertTrue(pc.getElementType() instanceof PGoBool);
		assertEquals(s, pt.toGoTypeName());

		s = "chan []int";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoChan);
		pc = (PGoChan) pt;
		assertTrue(pc.getElementType() instanceof PGoSlice);
		assertEquals(s, pt.toGoTypeName());
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
		assertTrue(ps.getElementType() instanceof PGoInt);
		assertEquals(s, ps.toGoTypeName());

		s = "set[]set[]bool";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSet);
		ps = (PGoSet) pt;
		assertTrue(ps.getElementType() instanceof PGoSet);
		ps = (PGoSet) ps.getElementType();
		assertTrue(ps.getElementType() instanceof PGoBool);
		assertEquals(s, pt.toGoTypeName());

		s = "set[][]int";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoSet);
		ps = (PGoSet) pt;
		assertTrue(ps.getElementType() instanceof PGoSlice);
		assertEquals(s, pt.toGoTypeName());
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
		assertTrue(pm.getKeyType() instanceof PGoInt);
		assertTrue(pm.getElementType() instanceof PGoBool);
		assertEquals(s, pm.toGoTypeName());

		s = "map[int]map[int]bool";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoMap);
		pm = (PGoMap) pt;
		assertTrue(pm.getKeyType() instanceof PGoInt);
		assertTrue(pm.getElementType() instanceof PGoMap);
		pm = (PGoMap) pm.getElementType();
		assertTrue(pm.getKeyType() instanceof PGoInt);
		assertTrue(pm.getElementType() instanceof PGoBool);
		assertEquals(s, pt.toGoTypeName());

		s = "map[string][]int";
		pt = PGoContainerType.inferContainerFromGoTypeName(s);
		assertTrue(pt instanceof PGoMap);
		pm = (PGoMap) pt;
		assertTrue(pm.getKeyType() instanceof PGoString);
		assertTrue(pm.getElementType() instanceof PGoSlice);
		assertEquals(s, pt.toGoTypeName());
	}
}
