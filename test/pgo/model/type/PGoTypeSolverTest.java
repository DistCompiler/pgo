package pgo.model.type;

import org.junit.Before;
import org.junit.Test;
import pgo.errors.IssueContext;
import pgo.errors.TopLevelIssueContext;
import pgo.scope.UID;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;

import static org.junit.Assert.*;

public class PGoTypeSolverTest {
	private PGoTypeSolver solver;
	private PGoTypeGenerator typeGenerator;
	private IssueContext ctx;
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
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, new PGoTypeTuple(Arrays.asList(a, b)), c));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		assertEquals(Collections.singletonMap(c, new PGoTypeTuple(Arrays.asList(a, b))), solver.getMapping());
	}

	@Test
	public void boolSlice() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, new PGoTypeBool()));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, b, new PGoTypeSlice(a)));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, new PGoTypeBool());
			put(b, new PGoTypeSlice(new PGoTypeBool()));
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
				new PGoTypeFunction(Collections.singletonList(a), b),
				new PGoTypeFunction(Collections.singletonList(b), c)));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				c,
				new PGoTypeFunction(Collections.singletonList(d), e)));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, new PGoTypeFunction(Collections.singletonList(d), e));
			put(b, new PGoTypeFunction(Collections.singletonList(d), e));
			put(c, new PGoTypeFunction(Collections.singletonList(d), e));
		}}, solver.getMapping());
	}

	@Test
	public void notUnifiable() {
		PGoTypeVariable a = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeBool(),
				new PGoTypeSet(new PGoTypeBool(), a)));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void infiniteType() {
		PGoTypeVariable a = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, new PGoTypeFunction(Collections.singletonList(new PGoTypeInt()), a)));
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
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, new PGoTypeSet(b)));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, b, new PGoTypeSet(a)));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void mismatchedSimpleContainerTypes() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, new PGoTypeSlice(a), new PGoTypeChan(b)));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void mismatchedNestedTypes() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeSet(new PGoTypeSlice(a)),
				new PGoTypeSet(new PGoTypeChan(b))));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void numberPromotion() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, b, new PGoTypeDecimal()));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, new PGoTypeUnrealizedNumber(new PGoTypeInt())));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, b));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, new PGoTypeDecimal());
			put(b, new PGoTypeDecimal());
		}}, solver.getMapping());
	}

	@Test
	public void tuplePromotion() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeTuple(Arrays.asList(new PGoTypeInt(), new PGoTypeString())),
				a));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeUnrealizedTuple(),
				b));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, b));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, new PGoTypeTuple(Arrays.asList(new PGoTypeInt(), new PGoTypeString())));
			put(b, new PGoTypeTuple(Arrays.asList(new PGoTypeInt(), new PGoTypeString())));
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
				new PGoTypeTuple(Arrays.asList(new PGoTypeInt(), d)),
				a));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeUnrealizedTuple(),
				b));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeUnrealizedTuple(Collections.singletonMap(1, new PGoTypeString())),
				c));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, b));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, b, c));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, new PGoTypeTuple(Arrays.asList(new PGoTypeInt(), new PGoTypeString())));
			put(b, new PGoTypeTuple(Arrays.asList(new PGoTypeInt(), new PGoTypeString())));
			put(c, new PGoTypeTuple(Arrays.asList(new PGoTypeInt(), new PGoTypeString())));
			put(d, new PGoTypeString());
		}}, solver.getMapping());
	}

	@Test
	public void complexTuplePromotion2() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		PGoTypeVariable c = typeGenerator.get();
		PGoTypeVariable d = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, new PGoTypeChan(d), a));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, new PGoTypeUnrealizedTuple(), b));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeUnrealizedTuple(Collections.singletonMap(0, new PGoTypeString())),
				c));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, b));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, b, c));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, new PGoTypeChan(new PGoTypeString()));
			put(b, new PGoTypeChan(new PGoTypeString()));
			put(c, new PGoTypeChan(new PGoTypeString()));
			put(d, new PGoTypeString());
		}}, solver.getMapping());
	}

	@Test
	public void unUnifiableTuplePromotion() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		PGoTypeVariable c = typeGenerator.get();
		PGoTypeVariable d = typeGenerator.get();
		PGoTypeVariable e = typeGenerator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, new PGoTypeChan(d), a));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, new PGoTypeUnrealizedTuple(), b));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeUnrealizedTuple(Collections.singletonMap(1, new PGoTypeString())),
				c));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeUnrealizedTuple(Collections.singletonMap(0, new PGoTypeInt())),
				e));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, b));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, b, c));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, e));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}
}