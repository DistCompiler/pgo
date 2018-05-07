package pgo.model.type;

import org.junit.Test;
import pgo.trans.PGoTransException;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.*;

public class PGoTypeGeneratorTest {
	static PGoTypeGenerator generator = new PGoTypeGenerator("test");

	@Test
	public void intSlice() throws PGoTransException {
		assertEquals(
				new PGoTypeSlice(PGoTypeInt.getInstance()),
				generator.inferFrom("[]int"));
	}

	@Test
	public void sliceOfBoolSlice() throws PGoTransException {
		assertEquals(
				new PGoTypeSlice(new PGoTypeSlice(PGoTypeBool.getInstance())),
				generator.inferFrom("[][]bool"));
	}

	@Test
	public void sliceOfMapIntBool() throws PGoTransException {
		assertEquals(
				new PGoTypeSlice(new PGoTypeMap(PGoTypeInt.getInstance(), PGoTypeBool.getInstance())),
				generator.inferFrom("[]map[int]bool"));
	}

	@Test
	public void sliceWithTypeVariable() throws PGoTransException {
		PGoType tn = generator.inferFrom("[]A");
		assertTrue(tn instanceof PGoTypeSlice);
		assertTrue(((PGoTypeSlice) tn).elementType instanceof PGoTypeVariable);
		assertTrue(tn.containsVariables());
	}

	@Test
	public void sliceOfSlicesWithTypeVariable() throws PGoTransException {
		PGoType tn = generator.inferFrom("[][]A");
		assertTrue(tn instanceof PGoTypeSlice);
		assertTrue(((PGoTypeSlice) tn).elementType instanceof PGoTypeSlice);
		assertTrue(((PGoTypeSlice) ((PGoTypeSlice) tn).elementType).elementType instanceof PGoTypeVariable);
		assertTrue(tn.containsVariables());
	}

	@Test
	public void intChan() throws PGoTransException {
		assertEquals(new PGoTypeChan(PGoTypeInt.getInstance()), generator.inferFrom("chan[int]"));
	}

	@Test
	public void chanOfBoolChan() throws PGoTransException {
		assertEquals(
				new PGoTypeChan(new PGoTypeChan(PGoTypeInt.getInstance())),
				generator.inferFrom("Chan[chan[int]]"));
	}

	@Test
	public void chanOfIntSlice() throws PGoTransException {
		assertEquals(
				new PGoTypeChan(new PGoTypeSlice(PGoTypeInt.getInstance())),
				generator.inferFrom("chan[[]int]"));
	}

	@Test
	public void chanWithTypeVariable() throws PGoTransException {
		PGoType tn = generator.inferFrom("chan[A]");
		assertTrue(tn instanceof PGoTypeChan);
		assertTrue(((PGoTypeChan) tn).elementType instanceof PGoTypeVariable);
		assertTrue(tn.containsVariables());
	}

	@Test
	public void chanOfChansWithTypeVariable() throws PGoTransException {
		PGoType tn = generator.inferFrom("chan[chan[A]]");
		assertTrue(tn instanceof PGoTypeChan);
		assertTrue(((PGoTypeChan) tn).elementType instanceof PGoTypeChan);
		assertTrue(((PGoTypeChan) ((PGoTypeChan) tn).elementType).elementType instanceof PGoTypeVariable);
		assertTrue(tn.containsVariables());
	}

	@Test
	public void intSet() throws PGoTransException {
		assertEquals(
				new PGoTypeSet(PGoTypeInt.getInstance()),
				generator.inferFrom("set[int]"));
	}

	@Test
	public void setOfBoolSets() throws PGoTransException {
		assertEquals(
				new PGoTypeSet(new PGoTypeSet(PGoTypeBool.getInstance())),
				generator.inferFrom("set[set[bool]]"));
	}

	@Test
	public void setOfBoolSlices() throws PGoTransException {
		assertEquals(
				new PGoTypeSet(new PGoTypeSlice(PGoTypeBool.getInstance())),
				generator.inferFrom("set[[]bool]"));
	}

	@Test
	public void setWithTypeVariable() throws PGoTransException {
		PGoType tn = generator.inferFrom("set[A]");
		assertTrue(tn instanceof PGoTypeSet);
		assertTrue(((PGoTypeSet) tn).elementType instanceof PGoTypeVariable);
		assertTrue(tn.containsVariables());
	}

	@Test
	public void setOfSetWithTypeVariable() throws PGoTransException {
		PGoType tn = generator.inferFrom("set[set[A]]");
		assertTrue(tn instanceof PGoTypeSet);
		assertTrue(((PGoTypeSet) tn).elementType instanceof PGoTypeSet);
		assertTrue(((PGoTypeSet) ((PGoTypeSet) tn).elementType).elementType instanceof PGoTypeVariable);
		assertTrue(tn.containsVariables());
	}

	@Test
	public void mapIntBool() throws PGoTransException {
		assertEquals(
				new PGoTypeMap(PGoTypeInt.getInstance(), PGoTypeBool.getInstance()),
				generator.inferFrom("map[int]bool"));
	}

	@Test
	public void mapIntMapIntBool() throws PGoTransException {
		assertEquals(
				new PGoTypeMap(
						PGoTypeInt.getInstance(),
						new PGoTypeMap(PGoTypeInt.getInstance(), PGoTypeBool.getInstance())),
				generator.inferFrom("map[int]map[int]bool"));
	}

	@Test
	public void mapStringIntSlice() throws PGoTransException {
		assertEquals(
				new PGoTypeMap(PGoTypeString.getInstance(), new PGoTypeSlice(PGoTypeInt.getInstance())),
				generator.inferFrom("map[string][]int"));
	}

	@Test
	public void mapIntTypeVariable() throws PGoTransException {
		PGoType tn = generator.inferFrom("map[int]A");
		assertTrue(tn instanceof PGoTypeMap);
		assertTrue(((PGoTypeMap) tn).getKeyType() instanceof PGoTypeInt);
		assertTrue(((PGoTypeMap) tn).getValueType() instanceof PGoTypeVariable);
		assertTrue(tn.containsVariables());
	}

	@Test
	public void mapIntMapIntTypeVariable() throws PGoTransException {
		PGoType tn = generator.inferFrom("map[int]map[int]A");
		assertTrue(tn instanceof PGoTypeMap);
		assertTrue(((PGoTypeMap) tn).getKeyType() instanceof PGoTypeInt);
		assertTrue(((PGoTypeMap) tn).getValueType() instanceof PGoTypeMap);
		assertTrue(((PGoTypeMap) ((PGoTypeMap) tn).getValueType()).getKeyType() instanceof PGoTypeInt);
		assertTrue(((PGoTypeMap) ((PGoTypeMap) tn).getValueType()).getValueType() instanceof PGoTypeVariable);
		assertTrue(tn.containsVariables());
	}

	@Test
	public void mapWithSameTypeVariable() throws PGoTransException {
		PGoType tn = generator.inferFrom("map[Z]Z");
		assertTrue(tn instanceof PGoTypeMap);
		assertTrue(((PGoTypeMap) tn).getKeyType() instanceof PGoTypeVariable);
		assertTrue(((PGoTypeMap) tn).getValueType() instanceof PGoTypeVariable);
		assertEquals(((PGoTypeMap) tn).getKeyType(), ((PGoTypeMap) tn).getValueType());
		assertTrue(tn.containsVariables());
	}

	@Test
	public void mapWithDifferentTypeVariables() throws PGoTransException {
		PGoType tn = generator.inferFrom("map[A]B");
		assertTrue(tn instanceof PGoTypeMap);
		assertTrue(((PGoTypeMap) tn).getKeyType() instanceof PGoTypeVariable);
		assertTrue(((PGoTypeMap) tn).getValueType() instanceof PGoTypeVariable);
		assertFalse(((PGoTypeMap) tn).getKeyType().equals(((PGoTypeMap) tn).getValueType()));
		assertTrue(tn.containsVariables());
	}

	@Test
	public void mapWithNestedTypeVariables() throws PGoTransException {
		PGoType tn = generator.inferFrom("map[C][]C");
		assertTrue(tn instanceof PGoTypeMap);
		assertTrue(((PGoTypeMap) tn).getKeyType() instanceof PGoTypeVariable);
		assertTrue(((PGoTypeMap) tn).getValueType() instanceof PGoTypeSlice);
		assertEquals(((PGoTypeSlice) ((PGoTypeMap) tn).getValueType()).elementType, ((PGoTypeMap) tn).getKeyType());
		assertTrue(tn.containsVariables());
	}

	@Test
	public void emptyTuple() throws PGoTransException {
		assertEquals(
				new PGoTypeTuple(new ArrayList<>()),
				generator.inferFrom("tuple[]"));
	}

	@Test
	public void complexTuple() throws PGoTransException {
		assertEquals(
				new PGoTypeTuple(Arrays.asList(
						PGoTypeInt.getInstance(),
						new PGoTypeMap(PGoTypeInt.getInstance(), PGoTypeString.getInstance()),
						new PGoTypeTuple(Collections.singletonList(PGoTypeString.getInstance())),
						PGoTypeString.getInstance())),
				generator.inferFrom("tuple[int, map[int]string, tuple[string], string]"));
	}

	@Test
	public void complexTuple2() throws PGoTransException {
		assertEquals(
				new PGoTypeTuple(Arrays.asList(
						PGoTypeInt.getInstance(),
						new PGoTypeTuple(Arrays.asList(PGoTypeDecimal.getInstance(), PGoTypeString.getInstance())),
						new PGoTypeSlice(PGoTypeInt.getInstance()))),
				generator.inferFrom("tuple[int, tuple[float64, string], []int]"));
	}

	@Test
	public void complexTupleWithTypeVariables() throws PGoTransException {
		PGoType tn = generator.inferFrom("tuple[E, map[F]G, tuple[E], F]");
		assertTrue(tn instanceof PGoTypeTuple);
		List<PGoType> ts = ((PGoTypeTuple) tn).getElementTypes();
		assertEquals(4, ts.size());
		assertTrue(ts.get(0) instanceof PGoTypeVariable);
		assertTrue(ts.get(1) instanceof PGoTypeMap);
		assertTrue(ts.get(2) instanceof PGoTypeTuple);
		assertTrue(ts.get(3) instanceof PGoTypeVariable);
		assertEquals(1, ((PGoTypeTuple) ts.get(2)).getElementTypes().size());
		assertEquals(ts.get(0), ((PGoTypeTuple) ts.get(2)).getElementTypes().get(0));
		assertEquals(ts.get(3), ((PGoTypeMap) ts.get(1)).getKeyType());
		assertTrue(tn.containsVariables());
	}
}