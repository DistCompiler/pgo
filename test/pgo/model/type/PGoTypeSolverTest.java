package pgo.model.type;

import org.junit.Before;
import org.junit.Test;
import pgo.errors.TopLevelIssueContext;
import pgo.scope.UID;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;

import static org.junit.Assert.*;

public class PGoTypeSolverTest {
	private PGoTypeSolver solver;
	private PGoTypeGenerator typeGenerator;
	private TopLevelIssueContext ctx;
	private UID dummyUID;

	@Before
	public void setup() {
		solver = new PGoTypeSolver();
		typeGenerator = new PGoTypeGenerator("a");
		ctx = new TopLevelIssueContext();
		dummyUID = new UID();
	}

	@Test
	public void simpleTypeVariables() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, b));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		assertEquals(Collections.singletonMap(a, b), solver.getMapping());
	}

	@Test
	public void simpleTuple() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		PGoTypeVariable c = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, new PGoTypeTuple(Arrays.asList(a, b), Collections.emptyList()), c));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		assertEquals(Collections.singletonMap(c, new PGoTypeTuple(Arrays.asList(a, b), Collections.emptyList())), solver.getMapping());
	}

	@Test
	public void boolSlice() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, new PGoTypeBool(Collections.emptyList())));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, b, new PGoTypeSlice(a, Collections.emptyList())));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, new PGoTypeBool(Collections.emptyList()));
			put(b, new PGoTypeSlice(new PGoTypeBool(Collections.emptyList()), Collections.emptyList()));
		}}, solver.getMapping());
	}

	@Test
	public void chainedFunctions() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		PGoTypeVariable c = typeGenerator.get();
		PGoTypeVariable d = typeGenerator.get();
		PGoTypeVariable e = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeFunction(Collections.singletonList(a), b, Collections.emptyList()),
				new PGoTypeFunction(Collections.singletonList(b), c, Collections.emptyList())));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				c,
				new PGoTypeFunction(Collections.singletonList(d), e, Collections.emptyList())));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, new PGoTypeFunction(Collections.singletonList(d), e, Collections.emptyList()));
			put(b, new PGoTypeFunction(Collections.singletonList(d), e, Collections.emptyList()));
			put(c, new PGoTypeFunction(Collections.singletonList(d), e, Collections.emptyList()));
		}}, solver.getMapping());
	}

	@Test
	public void notUnifiable() {
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeBool(Collections.emptyList()),
				new PGoTypeSet(new PGoTypeBool(Collections.emptyList()), Collections.emptyList())));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void infiniteType() {
		PGoTypeVariable a = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, new PGoTypeFunction(Collections.singletonList(new PGoTypeInt(Collections.emptyList())), a, Collections.emptyList())));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void circularConstraints() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, b));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, b, a));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		assertEquals(Collections.singletonMap(a, b), solver.getMapping());
	}

	@Test
	public void circularSets() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, new PGoTypeSet(b, Collections.emptyList())));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, b, new PGoTypeSet(a, Collections.emptyList())));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void mismatchedSimpleContainerTypes() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, new PGoTypeSlice(a, Collections.emptyList()), new PGoTypeChan(b, Collections.emptyList())));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void mismatchedNestedTypes() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeSet(new PGoTypeSlice(a, Collections.emptyList()), Collections.emptyList()),
				new PGoTypeSet(new PGoTypeChan(b, Collections.emptyList()), Collections.emptyList())));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void numberPromotion() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, b, new PGoTypeDecimal(Collections.emptyList())));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, new PGoTypeUnrealizedNumber(new PGoTypeInt(Collections.emptyList()), Collections.emptyList())));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, b));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, new PGoTypeDecimal(Collections.emptyList()));
			put(b, new PGoTypeDecimal(Collections.emptyList()));
		}}, solver.getMapping());
	}

	@Test
	public void tuplePromotion() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeTuple(Arrays.asList(new PGoTypeInt(Collections.emptyList()), new PGoTypeString(Collections.emptyList())), Collections.emptyList()),
				a));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeUnrealizedTuple(Collections.emptyList()),
				b));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, b));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, new PGoTypeTuple(Arrays.asList(new PGoTypeInt(Collections.emptyList()), new PGoTypeString(Collections.emptyList())), Collections.emptyList()));
			put(b, new PGoTypeTuple(Arrays.asList(new PGoTypeInt(Collections.emptyList()), new PGoTypeString(Collections.emptyList())), Collections.emptyList()));
		}}, solver.getMapping());
	}

	@Test
	public void complexTuplePromotion() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		PGoTypeVariable c = typeGenerator.get();
		PGoTypeVariable d = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeTuple(Arrays.asList(new PGoTypeInt(Collections.emptyList()), d), Collections.emptyList()),
				a));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeUnrealizedTuple(Collections.emptyList()),
				b));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeUnrealizedTuple(Collections.singletonMap(1, new PGoTypeString(Collections.emptyList())), Collections.emptyList()),
				c));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, b));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, b, c));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, new PGoTypeTuple(Arrays.asList(new PGoTypeInt(Collections.emptyList()), new PGoTypeString(Collections.emptyList())), Collections.emptyList()));
			put(b, new PGoTypeTuple(Arrays.asList(new PGoTypeInt(Collections.emptyList()), new PGoTypeString(Collections.emptyList())), Collections.emptyList()));
			put(c, new PGoTypeTuple(Arrays.asList(new PGoTypeInt(Collections.emptyList()), new PGoTypeString(Collections.emptyList())), Collections.emptyList()));
			put(d, new PGoTypeString(Collections.emptyList()));
		}}, solver.getMapping());
	}

	@Test
	public void complexTuplePromotion2() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		PGoTypeVariable c = typeGenerator.get();
		PGoTypeVariable d = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, new PGoTypeChan(d, Collections.emptyList()), a));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, new PGoTypeUnrealizedTuple(Collections.emptyList()), b));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeUnrealizedTuple(Collections.singletonMap(0, new PGoTypeString(Collections.emptyList())), Collections.emptyList()),
				c));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, b));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, b, c));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, new PGoTypeChan(new PGoTypeString(Collections.emptyList()), Collections.emptyList()));
			put(b, new PGoTypeChan(new PGoTypeString(Collections.emptyList()), Collections.emptyList()));
			put(c, new PGoTypeChan(new PGoTypeString(Collections.emptyList()), Collections.emptyList()));
			put(d, new PGoTypeString(Collections.emptyList()));
		}}, solver.getMapping());
	}

	@Test
	public void unUnifiableTuplePromotion() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		PGoTypeVariable c = typeGenerator.get();
		PGoTypeVariable d = typeGenerator.get();
		PGoTypeVariable e = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, new PGoTypeChan(d, Collections.emptyList()), a));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, new PGoTypeUnrealizedTuple(Collections.emptyList()), b));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeUnrealizedTuple(Collections.singletonMap(1, new PGoTypeString(Collections.emptyList())), Collections.emptyList()),
				c));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeUnrealizedTuple(Collections.singletonMap(0, new PGoTypeInt(Collections.emptyList())), Collections.emptyList()),
				e));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, b));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, b, c));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, e));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void setConstructionWithSlices() {
		// this represents code like the following
		//
		// a := Append(<<>>, 1);
		// b := {<<>>, <<1, 2>>, a};
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		PGoTypeVariable c = typeGenerator.get();
		PGoTypeVariable d = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, new PGoTypeUnrealizedTuple(Collections.emptyList())));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, new PGoTypeSlice(c, Collections.emptyList()), a));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, new PGoTypeUnrealizedNumber(new PGoTypeInt(Collections.emptyList()), Collections.emptyList()), c));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, b, new PGoTypeSlice(c, Collections.emptyList())));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, d, new PGoTypeUnrealizedTuple(Collections.emptyList())));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, d, new PGoTypeUnrealizedTuple(new HashMap<Integer, PGoType>() {{
			put(0, new PGoTypeUnrealizedNumber(new PGoTypeInt(Collections.emptyList()), Collections.emptyList()));
			put(1, new PGoTypeUnrealizedNumber(new PGoTypeInt(Collections.emptyList()), Collections.emptyList()));
		}}, Collections.emptyList())));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, d, a));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, new PGoTypeSlice(new PGoTypeInt(Collections.emptyList()), Collections.emptyList()));
			put(b, new PGoTypeSlice(new PGoTypeInt(Collections.emptyList()), Collections.emptyList()));
			put(c, new PGoTypeInt(Collections.emptyList()));
			put(d, new PGoTypeSlice(new PGoTypeInt(Collections.emptyList()), Collections.emptyList()));
		}}, solver.getMapping());
	}
}