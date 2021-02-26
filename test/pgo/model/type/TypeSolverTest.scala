package pgo.model.`type`

import pgo.errors.TopLevelIssueContext
import pgo.scope.UID

import java.util
import java.util.Collections
import org.scalatest.funsuite.AnyFunSuite
import pgo.model.`type`.constraint.MonomorphicConstraint

class TypeSolverTest extends AnyFunSuite{
  trait TSFixture {
    val solver = new TypeSolver()
    val typeGenerator = new TypeGenerator("a")
    val ctx = new TopLevelIssueContext()
    val dummyUID = new UID()
  }

  test("simpleTypeVariables")(new TSFixture {
    val a = typeGenerator.getTypeVariable(Collections.emptyList)
    val b = typeGenerator.getTypeVariable(Collections.emptyList)
    solver.addConstraint(new MonomorphicConstraint(dummyUID, a, b))
    solver.unify(ctx)
    assert(!ctx.hasErrors)
    val substitution = solver.getSubstitution
    assert(substitution.get(a) == substitution.get(b))
  })

  test("simpleTuple")(new TSFixture {
    val a = typeGenerator.getTypeVariable(Collections.emptyList)
    val b = typeGenerator.getTypeVariable(Collections.emptyList)
    val c = typeGenerator.getTypeVariable(Collections.emptyList)
    solver.addConstraint(new MonomorphicConstraint(dummyUID, new TupleType(util.Arrays.asList(a, b), Collections.emptyList), c))
    solver.unify(ctx)
    assert(!ctx.hasErrors)
    val substitution = solver.getSubstitution
    assert(new TupleType(util.Arrays.asList(a, b), Collections.emptyList) == substitution.get(c))
  })

  test("boolSlice")(new TSFixture {
    val a = typeGenerator.getTypeVariable(Collections.emptyList)
    val b = typeGenerator.getTypeVariable(Collections.emptyList)
    solver.addConstraint(new MonomorphicConstraint(dummyUID, a, new BoolType(Collections.emptyList)))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, b, new SliceType(a, Collections.emptyList)))
    solver.unify(ctx)
    assert(!ctx.hasErrors)
    val substitution = solver.getSubstitution
    assert(new BoolType(Collections.emptyList) == substitution.get(a))
    assert(new SliceType(new BoolType(Collections.emptyList), Collections.emptyList) == substitution.get(b))
  })

  test("mapStringInterface")(new TSFixture {
    val a = typeGenerator.getTypeVariable(Collections.emptyList)
    val b = typeGenerator.getTypeVariable(Collections.emptyList)
    solver.addConstraint(new MonomorphicConstraint(dummyUID, new MapType(new StringType(Collections.emptyList), new StringType(Collections.emptyList), Collections.emptyList), new MapType(a, b, Collections.emptyList)))
    solver.unify(ctx)
    assert(!ctx.hasErrors)
    val substitution = solver.getSubstitution
    assert(new StringType(Collections.emptyList) == substitution.get(a))
    assert(new StringType(Collections.emptyList) == substitution.get(b))
  })

  test("chainedFunctions")(new TSFixture {
    val a = typeGenerator.getTypeVariable(Collections.emptyList)
    val b = typeGenerator.getTypeVariable(Collections.emptyList)
    val c = typeGenerator.getTypeVariable(Collections.emptyList)
    val d = typeGenerator.getTypeVariable(Collections.emptyList)
    val e = typeGenerator.getTypeVariable(Collections.emptyList)
    solver.addConstraint(new MonomorphicConstraint(dummyUID, new FunctionType(Collections.singletonList(a), b, Collections.emptyList), new FunctionType(Collections.singletonList(b), c, Collections.emptyList)))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, c, new FunctionType(Collections.singletonList(d), e, Collections.emptyList)))
    solver.unify(ctx)
    assert(!ctx.hasErrors)
    val substitution = solver.getSubstitution
    assert(new FunctionType(Collections.singletonList(d), e, Collections.emptyList) == substitution.get(a))
    assert(new FunctionType(Collections.singletonList(d), e, Collections.emptyList) == substitution.get(b))
    assert(new FunctionType(Collections.singletonList(d), e, Collections.emptyList) == substitution.get(c))
  })

  test("notUnifiable")(new TSFixture {
    val a = typeGenerator.getTypeVariable(Collections.emptyList)
    solver.addConstraint(new MonomorphicConstraint(dummyUID, new BoolType(Collections.emptyList), new MapType(new BoolType(Collections.emptyList), a, Collections.emptyList)))
    solver.unify(ctx)
    assert(ctx.hasErrors)
  })

  test("infiniteType")(new TSFixture {
    val a = typeGenerator.getTypeVariable(Collections.emptyList)
    solver.addConstraint(new MonomorphicConstraint(dummyUID, a, new MapType(new IntType(Collections.emptyList), a, Collections.emptyList)))
    solver.unify(ctx)
    assert(ctx.hasErrors)
  })

  test("circularConstraints")(new TSFixture {
    val a = typeGenerator.getTypeVariable(Collections.emptyList)
    val b = typeGenerator.getTypeVariable(Collections.emptyList)
    solver.addConstraint(new MonomorphicConstraint(dummyUID, a, b))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, b, a))
    solver.unify(ctx)
    assert(!ctx.hasErrors)
    val substitution = solver.getSubstitution
    assert(substitution.get(a) == substitution.get(b))
  })

  test("circularSets")(new TSFixture {
    val a = typeGenerator.getTypeVariable(Collections.emptyList)
    val b = typeGenerator.getTypeVariable(Collections.emptyList)
    solver.addConstraint(new MonomorphicConstraint(dummyUID, a, new SetType(b, Collections.emptyList)))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, b, new SetType(a, Collections.emptyList)))
    solver.unify(ctx)
    assert(ctx.hasErrors)
  })

  test("mismatchedSimpleContainerTypes")(new TSFixture {
    val a = typeGenerator.getTypeVariable(Collections.emptyList)
    val b = typeGenerator.getTypeVariable(Collections.emptyList)
    solver.addConstraint(new MonomorphicConstraint(dummyUID, new SliceType(a, Collections.emptyList), new ChanType(b, Collections.emptyList)))
    solver.unify(ctx)
    assert(ctx.hasErrors)
  })

  test("mismatchedNestedTypes")(new TSFixture {
    val a = typeGenerator.getTypeVariable(Collections.emptyList)
    val b = typeGenerator.getTypeVariable(Collections.emptyList)
    solver.addConstraint(new MonomorphicConstraint(dummyUID, new SetType(new SliceType(a, Collections.emptyList), Collections.emptyList), new SetType(new ChanType(b, Collections.emptyList), Collections.emptyList)))
    solver.unify(ctx)
    assert(ctx.hasErrors)
  })

  test("abstractRecord")(new TSFixture {
    val a = typeGenerator.getTypeVariable(Collections.emptyList)
    val abstractRecord = typeGenerator.getAbstractRecord(Collections.emptyList)
    solver.addConstraint(new MonomorphicConstraint(dummyUID, a, abstractRecord))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, abstractRecord, "src", new StringType(Collections.emptyList)))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, abstractRecord, "ttl", new IntType(Collections.emptyList)))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, abstractRecord, "data", new StringType(Collections.emptyList)))
    solver.unify(ctx)
    assert(!ctx.hasErrors)
    val substitution = solver.getSubstitution
    assert(substitution.get(a) == new RecordType(util.Arrays.asList(new RecordType.Field("data", new StringType(Collections.emptyList)), new RecordType.Field("src", new StringType(Collections.emptyList)), new RecordType.Field("ttl", new IntType(Collections.emptyList))), Collections.emptyList))
  })

  test("indirectAbstractRecord")(new TSFixture {
    val a = typeGenerator.getTypeVariable(Collections.emptyList)
    val b = typeGenerator.getTypeVariable(Collections.emptyList)
    val c = typeGenerator.getTypeVariable(Collections.emptyList)
    val ar1 = typeGenerator.getAbstractRecord(Collections.emptyList)
    val ar2 = typeGenerator.getAbstractRecord(Collections.emptyList)
    val ar3 = typeGenerator.getAbstractRecord(Collections.emptyList)
    solver.addConstraint(new MonomorphicConstraint(dummyUID, a, ar1))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, ar1, "src", new StringType(Collections.emptyList)))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, b, ar2))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, ar2, "ttl", new IntType(Collections.emptyList)))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, c, ar3))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, ar3, "data", new StringType(Collections.emptyList)))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, a, b))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, c, b))
    solver.unify(ctx)
    assert(!ctx.hasErrors)
    val substitution = solver.getSubstitution
    assert(substitution.get(a) == substitution.get(b))
    assert(substitution.get(c) == substitution.get(b))
    assert(substitution.get(a) == new RecordType(util.Arrays.asList(new RecordType.Field("data", new StringType(Collections.emptyList)), new RecordType.Field("src", new StringType(Collections.emptyList)), new RecordType.Field("ttl", new IntType(Collections.emptyList))), Collections.emptyList))
  })

  test("concreteAndAbstractRecord")(new TSFixture {
    val a = typeGenerator.getTypeVariable(Collections.emptyList)
    val b = typeGenerator.getTypeVariable(Collections.emptyList)
    val c = typeGenerator.getTypeVariable(Collections.emptyList)
    val d = typeGenerator.getTypeVariable(Collections.emptyList)
    val ar1 = typeGenerator.getAbstractRecord(Collections.emptyList)
    val ar2 = typeGenerator.getAbstractRecord(Collections.emptyList)
    val ar3 = typeGenerator.getAbstractRecord(Collections.emptyList)
    solver.addConstraint(new MonomorphicConstraint(dummyUID, a, ar1))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, ar1, "src", new StringType(Collections.emptyList)))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, b, ar2))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, ar2, "ttl", new IntType(Collections.emptyList)))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, c, ar3))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, ar3, "data", new StringType(Collections.emptyList)))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, a, b))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, c, b))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, d, new RecordType(util.Arrays.asList(new RecordType.Field("src", new StringType(Collections.emptyList)), new RecordType.Field("ttl", new IntType(Collections.emptyList)), new RecordType.Field("data", new StringType(Collections.emptyList))), Collections.emptyList)))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, a, d))
    solver.unify(ctx)
    assert(!ctx.hasErrors)
    val substitution = solver.getSubstitution
    assert(substitution.get(a) == substitution.get(b))
    assert(substitution.get(c) == substitution.get(b))
    assert(substitution.get(a) == substitution.get(d))
    assert(substitution.get(a) == new RecordType(util.Arrays.asList(new RecordType.Field("src", new StringType(Collections.emptyList)), new RecordType.Field("ttl", new IntType(Collections.emptyList)), new RecordType.Field("data", new StringType(Collections.emptyList))), Collections.emptyList))
  })

  test("incompatibleConcreteAndAbstractRecord")(new TSFixture {
    val a = typeGenerator.getTypeVariable(Collections.emptyList)
    val b = typeGenerator.getTypeVariable(Collections.emptyList)
    val abstractRecord = typeGenerator.getAbstractRecord(Collections.emptyList)
    solver.addConstraint(new MonomorphicConstraint(dummyUID, a, abstractRecord))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, abstractRecord, "src", new StringType(Collections.emptyList)))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, abstractRecord, "ttl", new IntType(Collections.emptyList)))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, abstractRecord, "data", new StringType(Collections.emptyList)))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, b, new RecordType(util.Arrays.asList(new RecordType.Field("src", new StringType(Collections.emptyList)), new RecordType.Field("data", new StringType(Collections.emptyList))), Collections.emptyList)))
    solver.addConstraint(new MonomorphicConstraint(dummyUID, a, b))
    solver.unify(ctx)
    assert(ctx.hasErrors)
  })
}