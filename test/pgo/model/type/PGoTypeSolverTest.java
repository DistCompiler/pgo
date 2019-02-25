package pgo.model.type;

import org.junit.Before;
import org.junit.Test;
import pgo.errors.TopLevelIssueContext;
import pgo.scope.UID;

import java.util.Arrays;
import java.util.Collections;

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
		PGoTypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		PGoTypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, b));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		PGoTypeSubstitution substitution = solver.getSubstitution();
		assertEquals(substitution.get(a), substitution.get(b));
	}

	@Test
	public void simpleTuple() {
		PGoTypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		PGoTypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		PGoTypeVariable c = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID, new PGoTypeTuple(Arrays.asList(a, b), Collections.emptyList()), c));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		PGoTypeSubstitution substitution = solver.getSubstitution();
		assertEquals(new PGoTypeTuple(Arrays.asList(a, b), Collections.emptyList()), substitution.get(c));
	}

	@Test
	public void boolSlice() {
		PGoTypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		PGoTypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, new PGoTypeBool(Collections.emptyList())));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID, b, new PGoTypeSlice(a, Collections.emptyList())));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		PGoTypeSubstitution substitution = solver.getSubstitution();
		assertEquals(new PGoTypeBool(Collections.emptyList()), substitution.get(a));
		assertEquals(
				new PGoTypeSlice(new PGoTypeBool(Collections.emptyList()), Collections.emptyList()),
				substitution.get(b));
	}

	@Test
	public void mapStringInterface() {
		PGoTypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		PGoTypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeMap(
						new PGoTypeString(Collections.emptyList()),
						new PGoTypeString(Collections.emptyList()),
						Collections.emptyList()),
				new PGoTypeMap(a, b, Collections.emptyList())));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		PGoTypeSubstitution substitution = solver.getSubstitution();
		assertEquals(new PGoTypeString(Collections.emptyList()), substitution.get(a));
		assertEquals(new PGoTypeString(Collections.emptyList()), substitution.get(b));
	}

	@Test
	public void chainedFunctions() {
		PGoTypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		PGoTypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		PGoTypeVariable c = typeGenerator.getTypeVariable(Collections.emptyList());
		PGoTypeVariable d = typeGenerator.getTypeVariable(Collections.emptyList());
		PGoTypeVariable e = typeGenerator.getTypeVariable(Collections.emptyList());
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
		PGoTypeSubstitution substitution = solver.getSubstitution();
		assertEquals(
				new PGoTypeFunction(Collections.singletonList(d), e, Collections.emptyList()), substitution.get(a));
		assertEquals(
				new PGoTypeFunction(Collections.singletonList(d), e, Collections.emptyList()), substitution.get(b));
		assertEquals(
				new PGoTypeFunction(Collections.singletonList(d), e, Collections.emptyList()), substitution.get(c));
	}

	@Test
	public void notUnifiable() {
		PGoType a = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeBool(Collections.emptyList()),
				new PGoTypeMap(new PGoTypeBool(Collections.emptyList()), a, Collections.emptyList())));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void infiniteType() {
		PGoTypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID, a, new PGoTypeMap(new PGoTypeInt(Collections.emptyList()), a, Collections.emptyList())));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void circularConstraints() {
		PGoTypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		PGoTypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, b));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, b, a));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		PGoTypeSubstitution substitution = solver.getSubstitution();
		assertEquals(substitution.get(a), substitution.get(b));
	}

	@Test
	public void circularSets() {
		PGoTypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		PGoTypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, new PGoTypeSet(b, Collections.emptyList())));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, b, new PGoTypeSet(a, Collections.emptyList())));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void mismatchedSimpleContainerTypes() {
		PGoTypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		PGoTypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID, new PGoTypeSlice(a, Collections.emptyList()), new PGoTypeChan(b, Collections.emptyList())));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void mismatchedNestedTypes() {
		PGoTypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		PGoTypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID,
				new PGoTypeSet(new PGoTypeSlice(a, Collections.emptyList()), Collections.emptyList()),
				new PGoTypeSet(new PGoTypeChan(b, Collections.emptyList()), Collections.emptyList())));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void abstractRecord() {
		PGoTypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		PGoTypeAbstractRecord abstractRecord = typeGenerator.getAbstractRecord(Collections.emptyList());
		solver.addConstraint(new PGoTypeMonomorphicConstraint(dummyUID, a, abstractRecord));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID, abstractRecord, "src", new PGoTypeString(Collections.emptyList())));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID, abstractRecord, "ttl", new PGoTypeInt(Collections.emptyList())));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				dummyUID, abstractRecord, "data", new PGoTypeString(Collections.emptyList())));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		PGoTypeSubstitution substitution = solver.getSubstitution();
		assertEquals(
				substitution.get(a),
				new PGoTypeRecord(
						Arrays.asList(
								new PGoTypeRecord.Field("data", new PGoTypeString(Collections.emptyList())),
								new PGoTypeRecord.Field("src", new PGoTypeString(Collections.emptyList())),
								new PGoTypeRecord.Field("ttl", new PGoTypeInt(Collections.emptyList()))),
						Collections.emptyList()));
	}
}
