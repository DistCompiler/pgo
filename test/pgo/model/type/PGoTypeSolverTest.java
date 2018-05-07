package pgo.model.type;

import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;

import static org.junit.Assert.*;

public class PGoTypeSolverTest {
	private PGoTypeSolver solver;
	private PGoTypeGenerator typeGenerator;

	@Before
	public void setup() {
		solver = new PGoTypeSolver();
		typeGenerator = new PGoTypeGenerator("a");
	}

	@Test
	public void simpleTypeVariables() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.accept(new PGoTypeConstraint(a, b, -1));
		solver.unify();
		assertEquals(Collections.singletonMap(a, b), solver.getMapping());
	}

	@Test
	public void simpleTuple() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		PGoTypeVariable c = typeGenerator.get();
		solver.accept(new PGoTypeConstraint(new PGoTypeTuple(Arrays.asList(a, b)), c, -1));
		solver.unify();
		assertEquals(Collections.singletonMap(c, new PGoTypeTuple(Arrays.asList(a, b))), solver.getMapping());
	}

	@Test
	public void boolSlice() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.accept(new PGoTypeConstraint(a, PGoTypeBool.getInstance(), -1));
		solver.accept(new PGoTypeConstraint(b, new PGoTypeSlice(a), -1));
		solver.unify();
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, PGoTypeBool.getInstance());
			put(b, new PGoTypeSlice(PGoTypeBool.getInstance()));
		}}, solver.getMapping());
	}

	@Test
	public void mapStringInterface() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.accept(new PGoTypeConstraint(
				new PGoTypeMap(PGoTypeString.getInstance(), PGoTypeInterface.getInstance()),
				new PGoTypeMap(a, b),
				-1));
		solver.unify();
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, PGoTypeString.getInstance());
			put(b, PGoTypeInterface.getInstance());
		}}, solver.getMapping());
	}

	@Test
	public void chainedFunctions() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		PGoTypeVariable c = typeGenerator.get();
		PGoTypeVariable d = typeGenerator.get();
		PGoTypeVariable e = typeGenerator.get();
		solver.accept(new PGoTypeConstraint(
				new PGoTypeFunction(Collections.singletonList(a), b),
				new PGoTypeFunction(Collections.singletonList(b), c),
				-1));
		solver.accept(new PGoTypeConstraint(c, new PGoTypeFunction(Collections.singletonList(d), e), -1));
		solver.unify();
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, new PGoTypeFunction(Collections.singletonList(d), e));
			put(b, new PGoTypeFunction(Collections.singletonList(d), e));
			put(c, new PGoTypeFunction(Collections.singletonList(d), e));
		}}, solver.getMapping());
	}

	@Test(expected = PGoTypeUnificationException.class)
	public void notUnifiable() {
		PGoTypeVariable a = typeGenerator.get();
		solver.accept(new PGoTypeConstraint(
				PGoTypeError.getInstance(),
				new PGoTypeMap(PGoTypeError.getInstance(), a),
				-1));
		solver.unify();
	}

	@Test(expected = PGoTypeUnificationException.class)
	public void infiniteType() {
		PGoTypeVariable a = typeGenerator.get();
		solver.accept(new PGoTypeConstraint(a, new PGoTypeMap(PGoTypeVoid.getInstance(), a), -1));
		solver.unify();
	}

	@Test
	public void circularConstraints() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.accept(new PGoTypeConstraint(a, b, -1));
		solver.accept(new PGoTypeConstraint(b, a, -1));
		solver.unify();
		assertEquals(Collections.singletonMap(b, a), solver.getMapping());
	}

	@Test(expected = PGoTypeUnificationException.class)
	public void circularSets() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.accept(new PGoTypeConstraint(a, new PGoTypeSet(b), -1));
		solver.accept(new PGoTypeConstraint(b, new PGoTypeSet(a), -1));
		solver.unify();
	}

	@Test(expected = PGoTypeUnificationException.class)
	public void mismatchedSimpleContainerTypes() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.accept(new PGoTypeConstraint(new PGoTypeSlice(a), new PGoTypeChan(b), -1));
		solver.unify();
	}

	@Test(expected = PGoTypeUnificationException.class)
	public void mismatchedNestedTypes() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.accept(new PGoTypeConstraint(
				new PGoTypeSet(new PGoTypeSlice(a)),
				new PGoTypeSet(new PGoTypeChan(b)),
				-1));
		solver.unify();
	}

	@Test
	public void numberPromotion() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.accept(new PGoTypeConstraint(b, new PGoTypeUnrealizedNumber(PGoTypeDecimal.getInstance()), -1));
		solver.accept(new PGoTypeConstraint(a, new PGoTypeUnrealizedNumber(), -1));
		solver.accept(new PGoTypeConstraint(a, b, -1));
		solver.unify();
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, PGoTypeDecimal.getInstance());
			put(b, PGoTypeDecimal.getInstance());
		}}, solver.getMapping());
	}

	@Test(expected = PGoTypeUnificationException.class)
	public void boundedNumberPromotion() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.accept(new PGoTypeConstraint(b, new PGoTypeUnrealizedNumber(PGoTypeDecimal.getInstance()), -1));
		solver.accept(new PGoTypeConstraint(a, PGoTypeUnrealizedNumber.integralType(), -1));
		solver.accept(new PGoTypeConstraint(a, b, -1));
		solver.unify();
	}

	@Test
	public void tuplePromotion() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		solver.accept(new PGoTypeConstraint(
				new PGoTypeTuple(Arrays.asList(PGoTypeInt.getInstance(), PGoTypeString.getInstance())),
				a,
				-1));
		solver.accept(new PGoTypeConstraint(
				new PGoTypeUnrealizedTuple(),
				b,
				-1));
		solver.accept(new PGoTypeConstraint(a, b, -1));
		solver.unify();
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, new PGoTypeTuple(Arrays.asList(PGoTypeInt.getInstance(), PGoTypeString.getInstance())));
			put(b, new PGoTypeTuple(Arrays.asList(PGoTypeInt.getInstance(), PGoTypeString.getInstance())));
		}}, solver.getMapping());
	}

	@Test
	public void complexTuplePromotion() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		PGoTypeVariable c = typeGenerator.get();
		PGoTypeVariable d = typeGenerator.get();
		solver.accept(new PGoTypeConstraint(
				new PGoTypeTuple(Arrays.asList(PGoTypeInt.getInstance(), d)),
				a,
				-1));
		solver.accept(new PGoTypeConstraint(
				new PGoTypeUnrealizedTuple(),
				b,
				-1));
		solver.accept(new PGoTypeConstraint(
				new PGoTypeUnrealizedTuple(Collections.singletonMap(1, PGoTypeString.getInstance())),
				c,
				-1));
		solver.accept(new PGoTypeConstraint(a, b, -1));
		solver.accept(new PGoTypeConstraint(b, c, -1));
		solver.unify();
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, new PGoTypeTuple(Arrays.asList(PGoTypeInt.getInstance(), PGoTypeString.getInstance())));
			put(b, new PGoTypeTuple(Arrays.asList(PGoTypeInt.getInstance(), PGoTypeString.getInstance())));
			put(c, new PGoTypeTuple(Arrays.asList(PGoTypeInt.getInstance(), PGoTypeString.getInstance())));
			put(d, PGoTypeString.getInstance());
		}}, solver.getMapping());
	}

	@Test
	public void complexTuplePromotion2() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		PGoTypeVariable c = typeGenerator.get();
		PGoTypeVariable d = typeGenerator.get();
		solver.accept(new PGoTypeConstraint(new PGoTypeChan(d), a, -1));
		solver.accept(new PGoTypeConstraint(new PGoTypeUnrealizedTuple(), b, -1));
		solver.accept(new PGoTypeConstraint(
				new PGoTypeUnrealizedTuple(Collections.singletonMap(0, PGoTypeString.getInstance())),
				c,
				-1));
		solver.accept(new PGoTypeConstraint(a, b, -1));
		solver.accept(new PGoTypeConstraint(b, c, -1));
		solver.unify();
		assertEquals(new HashMap<PGoTypeVariable, PGoType>() {{
			put(a, new PGoTypeChan(PGoTypeString.getInstance()));
			put(b, new PGoTypeChan(PGoTypeString.getInstance()));
			put(c, new PGoTypeChan(PGoTypeString.getInstance()));
			put(d, PGoTypeString.getInstance());
		}}, solver.getMapping());
	}

	@Test(expected = PGoTypeUnificationException.class)
	public void unUnifiableTuplePromotion() {
		PGoTypeVariable a = typeGenerator.get();
		PGoTypeVariable b = typeGenerator.get();
		PGoTypeVariable c = typeGenerator.get();
		PGoTypeVariable d = typeGenerator.get();
		solver.accept(new PGoTypeConstraint(new PGoTypeChan(d), a, -1));
		solver.accept(new PGoTypeConstraint(new PGoTypeUnrealizedTuple(), b, -1));
		solver.accept(new PGoTypeConstraint(
				new PGoTypeUnrealizedTuple(Collections.singletonMap(1, PGoTypeString.getInstance())),
				c,
				-1));
		solver.accept(new PGoTypeConstraint(a, b, -1));
		solver.accept(new PGoTypeConstraint(b, c, -1));
		solver.unify();
	}
}