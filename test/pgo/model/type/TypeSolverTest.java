package pgo.model.type;

import org.junit.Before;
import org.junit.Test;
import pgo.errors.TopLevelIssueContext;
import pgo.model.type.constraint.MonomorphicConstraint;
import pgo.scope.UID;

import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.*;

public class TypeSolverTest {
	private TypeSolver solver;
	private TypeGenerator typeGenerator;
	private TopLevelIssueContext ctx;
	private UID dummyUID;

	@Before
	public void setup() {
		solver = new TypeSolver();
		typeGenerator = new TypeGenerator("a");
		ctx = new TopLevelIssueContext();
		dummyUID = new UID();
	}

	@Test
	public void simpleTypeVariables() {
		TypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new MonomorphicConstraint(dummyUID, a, b));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		TypeSubstitution substitution = solver.getSubstitution();
		assertEquals(substitution.get(a), substitution.get(b));
	}

	@Test
	public void simpleTuple() {
		TypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable c = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID, new TupleType(Arrays.asList(a, b), Collections.emptyList()), c));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		TypeSubstitution substitution = solver.getSubstitution();
		assertEquals(new TupleType(Arrays.asList(a, b), Collections.emptyList()), substitution.get(c));
	}

	@Test
	public void boolSlice() {
		TypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new MonomorphicConstraint(dummyUID, a, new BoolType(Collections.emptyList())));
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID, b, new SliceType(a, Collections.emptyList())));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		TypeSubstitution substitution = solver.getSubstitution();
		assertEquals(new BoolType(Collections.emptyList()), substitution.get(a));
		assertEquals(
				new SliceType(new BoolType(Collections.emptyList()), Collections.emptyList()),
				substitution.get(b));
	}

	@Test
	public void mapStringInterface() {
		TypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID,
				new MapType(
						new StringType(Collections.emptyList()),
						new StringType(Collections.emptyList()),
						Collections.emptyList()),
				new MapType(a, b, Collections.emptyList())));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		TypeSubstitution substitution = solver.getSubstitution();
		assertEquals(new StringType(Collections.emptyList()), substitution.get(a));
		assertEquals(new StringType(Collections.emptyList()), substitution.get(b));
	}

	@Test
	public void chainedFunctions() {
		TypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable c = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable d = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable e = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID,
				new FunctionType(Collections.singletonList(a), b, Collections.emptyList()),
				new FunctionType(Collections.singletonList(b), c, Collections.emptyList())));
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID,
				c,
				new FunctionType(Collections.singletonList(d), e, Collections.emptyList())));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		TypeSubstitution substitution = solver.getSubstitution();
		assertEquals(
				new FunctionType(Collections.singletonList(d), e, Collections.emptyList()), substitution.get(a));
		assertEquals(
				new FunctionType(Collections.singletonList(d), e, Collections.emptyList()), substitution.get(b));
		assertEquals(
				new FunctionType(Collections.singletonList(d), e, Collections.emptyList()), substitution.get(c));
	}

	@Test
	public void notUnifiable() {
		Type a = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID,
				new BoolType(Collections.emptyList()),
				new MapType(new BoolType(Collections.emptyList()), a, Collections.emptyList())));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void infiniteType() {
		TypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID, a, new MapType(new IntType(Collections.emptyList()), a, Collections.emptyList())));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void circularConstraints() {
		TypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new MonomorphicConstraint(dummyUID, a, b));
		solver.addConstraint(new MonomorphicConstraint(dummyUID, b, a));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		TypeSubstitution substitution = solver.getSubstitution();
		assertEquals(substitution.get(a), substitution.get(b));
	}

	@Test
	public void circularSets() {
		TypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new MonomorphicConstraint(dummyUID, a, new SetType(b, Collections.emptyList())));
		solver.addConstraint(new MonomorphicConstraint(dummyUID, b, new SetType(a, Collections.emptyList())));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void mismatchedSimpleContainerTypes() {
		TypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID, new SliceType(a, Collections.emptyList()), new ChanType(b, Collections.emptyList())));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void mismatchedNestedTypes() {
		TypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID,
				new SetType(new SliceType(a, Collections.emptyList()), Collections.emptyList()),
				new SetType(new ChanType(b, Collections.emptyList()), Collections.emptyList())));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}

	@Test
	public void abstractRecord() {
		TypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		AbstractRecordType abstractRecord = typeGenerator.getAbstractRecord(Collections.emptyList());
		solver.addConstraint(new MonomorphicConstraint(dummyUID, a, abstractRecord));
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID, abstractRecord, "src", new StringType(Collections.emptyList())));
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID, abstractRecord, "ttl", new IntType(Collections.emptyList())));
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID, abstractRecord, "data", new StringType(Collections.emptyList())));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		TypeSubstitution substitution = solver.getSubstitution();
		assertEquals(
				substitution.get(a),
				new RecordType(
						Arrays.asList(
								new RecordType.Field("data", new StringType(Collections.emptyList())),
								new RecordType.Field("src", new StringType(Collections.emptyList())),
								new RecordType.Field("ttl", new IntType(Collections.emptyList()))),
						Collections.emptyList()));
	}

	@Test
	public void indirectAbstractRecord() {
		TypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable c = typeGenerator.getTypeVariable(Collections.emptyList());
		AbstractRecordType ar1 = typeGenerator.getAbstractRecord(Collections.emptyList());
		AbstractRecordType ar2 = typeGenerator.getAbstractRecord(Collections.emptyList());
		AbstractRecordType ar3 = typeGenerator.getAbstractRecord(Collections.emptyList());
		solver.addConstraint(new MonomorphicConstraint(dummyUID, a, ar1));
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID, ar1, "src", new StringType(Collections.emptyList())));
		solver.addConstraint(new MonomorphicConstraint(dummyUID, b, ar2));
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID, ar2, "ttl", new IntType(Collections.emptyList())));
		solver.addConstraint(new MonomorphicConstraint(dummyUID, c, ar3));
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID, ar3, "data", new StringType(Collections.emptyList())));
		solver.addConstraint(new MonomorphicConstraint(dummyUID, a, b));
		solver.addConstraint(new MonomorphicConstraint(dummyUID, c, b));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		TypeSubstitution substitution = solver.getSubstitution();
		assertEquals(substitution.get(a), substitution.get(b));
		assertEquals(substitution.get(c), substitution.get(b));
		assertEquals(
				substitution.get(a),
				new RecordType(
						Arrays.asList(
								new RecordType.Field("data", new StringType(Collections.emptyList())),
								new RecordType.Field("src", new StringType(Collections.emptyList())),
								new RecordType.Field("ttl", new IntType(Collections.emptyList()))),
						Collections.emptyList()));
	}

	@Test
	public void concreteAndAbstractRecord() {
		TypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable c = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable d = typeGenerator.getTypeVariable(Collections.emptyList());
		AbstractRecordType ar1 = typeGenerator.getAbstractRecord(Collections.emptyList());
		AbstractRecordType ar2 = typeGenerator.getAbstractRecord(Collections.emptyList());
		AbstractRecordType ar3 = typeGenerator.getAbstractRecord(Collections.emptyList());
		solver.addConstraint(new MonomorphicConstraint(dummyUID, a, ar1));
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID, ar1, "src", new StringType(Collections.emptyList())));
		solver.addConstraint(new MonomorphicConstraint(dummyUID, b, ar2));
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID, ar2, "ttl", new IntType(Collections.emptyList())));
		solver.addConstraint(new MonomorphicConstraint(dummyUID, c, ar3));
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID, ar3, "data", new StringType(Collections.emptyList())));
		solver.addConstraint(new MonomorphicConstraint(dummyUID, a, b));
		solver.addConstraint(new MonomorphicConstraint(dummyUID, c, b));
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID,
				d,
				new RecordType(
						Arrays.asList(
								new RecordType.Field("src", new StringType(Collections.emptyList())),
								new RecordType.Field("ttl", new IntType(Collections.emptyList())),
								new RecordType.Field("data", new StringType(Collections.emptyList()))),
						Collections.emptyList())));
		solver.addConstraint(new MonomorphicConstraint(dummyUID, a, d));
		solver.unify(ctx);
		assertFalse(ctx.hasErrors());
		TypeSubstitution substitution = solver.getSubstitution();
		assertEquals(substitution.get(a), substitution.get(b));
		assertEquals(substitution.get(c), substitution.get(b));
		assertEquals(substitution.get(a), substitution.get(d));
		assertEquals(
				substitution.get(a),
				new RecordType(
						Arrays.asList(
								new RecordType.Field("src", new StringType(Collections.emptyList())),
								new RecordType.Field("ttl", new IntType(Collections.emptyList())),
								new RecordType.Field("data", new StringType(Collections.emptyList()))),
						Collections.emptyList()));
	}

	@Test
	public void incompatibleConcreteAndAbstractRecord() {
		TypeVariable a = typeGenerator.getTypeVariable(Collections.emptyList());
		TypeVariable b = typeGenerator.getTypeVariable(Collections.emptyList());
		AbstractRecordType abstractRecord = typeGenerator.getAbstractRecord(Collections.emptyList());
		solver.addConstraint(new MonomorphicConstraint(dummyUID, a, abstractRecord));
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID, abstractRecord, "src", new StringType(Collections.emptyList())));
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID, abstractRecord, "ttl", new IntType(Collections.emptyList())));
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID, abstractRecord, "data", new StringType(Collections.emptyList())));
		solver.addConstraint(new MonomorphicConstraint(
				dummyUID,
				b,
				new RecordType(
						Arrays.asList(
								new RecordType.Field("src", new StringType(Collections.emptyList())),
								new RecordType.Field("data", new StringType(Collections.emptyList()))),
						Collections.emptyList())));
		solver.addConstraint(new MonomorphicConstraint(dummyUID, a, b));
		solver.unify(ctx);
		assertTrue(ctx.hasErrors());
	}
}
