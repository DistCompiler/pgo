package pgo.model.type;

import pgo.InternalCompilerError;
import pgo.Unreachable;
import pgo.errors.Issue;
import pgo.errors.IssueContext;
import pgo.model.type.constraint.*;
import pgo.util.UnionFind;

import java.util.*;
import java.util.stream.Collectors;

/**
 * A constraint solver for PGo's type system. It does not support recursive types.
 */
public class TypeSolver {
	private Deque<Constraint> constraints = new ArrayDeque<>();
	private Map<TypeVariable, Type> mapping = new HashMap<>();
	private UnionFind<TypeVariable> variableGroups = new UnionFind<>();
	private UnionFind<AbstractRecordType> abstractRecordGroups = new UnionFind<>();
	private Map<AbstractRecordType, RecordTypeEntry> abstractRecordsToEntries = new HashMap<>();
	private Deque<TypeSolver> stateStack = new ArrayDeque<>();
	private int lastConstraintsSize = Integer.MAX_VALUE;
	private Issue typeInferenceIssue = null;

	private TypeVariableSubstitutionVisitor subs = new TypeVariableSubstitutionVisitor(
			new TypeSubstitution(variableGroups, mapping));

	public TypeSubstitution getSubstitution() {
		return new TypeSubstitution(variableGroups, mapping);
	}

	public void addConstraint(Constraint constraint) {
		constraints.addLast(constraint);
	}

	void addFirst(Constraint constraint) {
		constraints.addFirst(constraint);
	}

	private Optional<Issue> backtrack(Issue issue) {
		if (lastConstraintsSize > constraints.size()) {
			lastConstraintsSize = constraints.size();
			typeInferenceIssue = issue;
		}
		if (stateStack.size() <= 0) {
			// unsuccessful
			return Optional.of(typeInferenceIssue);
		}
		TypeSolver old = stateStack.pop();
		constraints = old.constraints;
		mapping = old.mapping;
		variableGroups = old.variableGroups;
		abstractRecordGroups = old.abstractRecordGroups;
		abstractRecordsToEntries = old.abstractRecordsToEntries;
		stateStack = old.stateStack;
		subs = new TypeVariableSubstitutionVisitor(
				new TypeSubstitution(variableGroups, mapping));
		return Optional.empty();
	}

	private TypeSolver copy() {
		TypeSolver copy = new TypeSolver();
		copy.stateStack = new ArrayDeque<>(stateStack);
		copy.constraints = constraints.stream()
				.map(Constraint::copy)
				.collect(Collectors.toCollection(ArrayDeque::new));
		copy.mapping = new HashMap<>();
		copy.variableGroups = variableGroups.copy();
		copy.abstractRecordGroups = abstractRecordGroups.copy();
		copy.abstractRecordsToEntries = new HashMap<>(abstractRecordsToEntries);
		TypeCopyVisitor visitor = new TypeCopyVisitor();
		mapping.forEach((k, v) -> copy.mapping.put(k, v.accept(visitor)));
		copy.subs = null;
		return copy;
	}

	private void simplify() {
		TypeVariableAbstractRecordSubstitutionVisitor tvarSubs =
				new TypeVariableAbstractRecordSubstitutionVisitor(
						getSubstitution(), abstractRecordGroups, abstractRecordsToEntries);
		boolean changed = true;
		while (changed) {
			changed = false;
			for (Map.Entry<TypeVariable, Type> entry : mapping.entrySet()) {
				TypeVariable k = entry.getKey();
				Type v = entry.getValue();
				Type newV = v.accept(tvarSubs);
				if (!newV.equals(v)) {
					changed = true;
					mapping.put(k, newV);
				}
			}
		}
	}

	private Optional<Issue> unify() {
		lastConstraintsSize = constraints.size();
		while (constraints.size() != 0) {
			Constraint constraint = constraints.removeFirst();
			if (constraint instanceof PolymorphicConstraint) {
				if (!((PolymorphicConstraint) constraint).hasNext()) {
					return Optional.of(new BacktrackingFailureIssue((PolymorphicConstraint) constraint));
				}
				// extract first constraints
				List<BasicConstraint> basicConstraints = ((PolymorphicConstraint) constraint).next();
				// snapshot state if there are any constraints left
				if (((PolymorphicConstraint) constraint).hasNext()) {
					// push copy with current constraint added at front
					TypeSolver copy = copy();
					copy.constraints.addFirst(constraint.copy());
					stateStack.push(copy);
				}
				// add the first constraints
				for (BasicConstraint basicConstraint : basicConstraints) {
					constraints.addFirst(new MonomorphicConstraint(constraint.getOrigins(), basicConstraint));
				}
				// solve the newly added constraints
				continue;
			}
			if (!(constraint instanceof MonomorphicConstraint)) {
				throw new Unreachable();
			}
			BasicConstraint basicConstraint = ((MonomorphicConstraint) constraint).getBasicConstraint();
			if (basicConstraint instanceof HasFieldConstraint) {
				HasFieldConstraint hasFieldConstraint = (HasFieldConstraint) basicConstraint;
				Type expressionType = hasFieldConstraint.getExpressionType();
				String fieldName = hasFieldConstraint.getFieldName();
				Type fieldType = hasFieldConstraint.getFieldType();
				if (expressionType instanceof RecordType) {
					if (((RecordType) expressionType).getFields().stream().noneMatch(f -> {
						if (f.getName().equals(fieldName)) {
							addFirst(new MonomorphicConstraint(constraint, fieldType, f.getType()));
							return true;
						}
						return false;
					})) {
						Optional<Issue> optionalIssue =
								backtrack(new NoMatchingFieldIssue((RecordType) expressionType, fieldName));
						if (optionalIssue.isPresent()) {
							return optionalIssue;
						}
						continue;
					}
					continue;
				}
				if (expressionType instanceof AbstractRecordType) {
					AbstractRecordType abstractRecord =
							abstractRecordGroups.find((AbstractRecordType) expressionType);
					if (abstractRecordsToEntries.containsKey(abstractRecord)) {
						try {
							abstractRecordsToEntries.put(
									abstractRecord,
									abstractRecordsToEntries.get(abstractRecord)
											.unify(
													this,
													new RecordTypeEntry.Abstract(
															Collections.singletonMap(fieldName, fieldType))));
						} catch (UnificationException e) {
							Optional<Issue> optionalIssue = backtrack(e.getIssue());
							if (optionalIssue.isPresent()) {
								return optionalIssue;
							}
							continue;
						}
					} else {
						abstractRecordsToEntries.put(
								abstractRecord,
								new RecordTypeEntry.Abstract(Collections.singletonMap(fieldName, fieldType)));
					}
					continue;
				}
				throw new InternalCompilerError();
			}
			if (!(basicConstraint instanceof EqualityConstraint)) {
				throw new InternalCompilerError();
			}
			Type a = ((EqualityConstraint) basicConstraint).getLhs();
			Type b = ((EqualityConstraint) basicConstraint).getRhs();
			if (a instanceof TypeVariable && b instanceof TypeVariable) {
				// find the variable groups to which a and b belong
				a = variableGroups.find((TypeVariable) a);
				b = variableGroups.find((TypeVariable) b);
				// get the previous types to which a and b maps
				Type subbedA = a.accept(subs);
				Type subbedB = b.accept(subs);
				// union the two groups to which a and b belong
				variableGroups.union((TypeVariable) a, (TypeVariable) b);
				// add constraints for the group representative
				TypeVariable groupRepresentative = variableGroups.find((TypeVariable) a);
				if (!a.equals(groupRepresentative)) {
					mapping.remove(a);
					constraints.addFirst(new MonomorphicConstraint(
							Collections.emptyList(), new EqualityConstraint(groupRepresentative, subbedA)));
				}
				if (!b.equals(groupRepresentative)) {
					mapping.remove(b);
					constraints.addFirst(new MonomorphicConstraint(
							Collections.emptyList(), new EqualityConstraint(groupRepresentative, subbedB)));
				}
				continue;
			}
			TypeVariable groupRepresentative = null;
			if (a instanceof TypeVariable) {
				// find the variable group to which a belongs
				groupRepresentative = variableGroups.find((TypeVariable) a);
				a = groupRepresentative;
			}
			if (b instanceof TypeVariable) {
				// find the variable group to which b belongs
				groupRepresentative = variableGroups.find((TypeVariable) b);
				// swap a and b
				b = a;
				a = groupRepresentative;
			}
			// a and b are substituted so that we gain more information about their structures
			a = a.accept(subs);
			b = b.accept(subs);
			// resolve abstract records
			if (a instanceof AbstractRecordType && b instanceof AbstractRecordType) {
				// find the variable groups to which a and b belong
				a = abstractRecordGroups.find((AbstractRecordType) a);
				b = abstractRecordGroups.find((AbstractRecordType) b);
				// get the previous entries to which a and b maps
				RecordTypeEntry entryA = abstractRecordsToEntries.getOrDefault(
						a, RecordTypeEntry.Abstract.EMPTY_ABSTRACT_RECORD);
				RecordTypeEntry entryB = abstractRecordsToEntries.getOrDefault(
						b, RecordTypeEntry.Abstract.EMPTY_ABSTRACT_RECORD);
				// union the two groups to which a and b belong
				abstractRecordGroups.union((AbstractRecordType) a, (AbstractRecordType) b);
				// add constraints for the group representative
				try {
					AbstractRecordType rep = abstractRecordGroups.find((AbstractRecordType) a);
					if (!a.equals(rep)) {
						abstractRecordsToEntries.remove(a);
						entryA = entryA.unify(this, abstractRecordsToEntries.get(rep));
					}
					if (!b.equals(rep)) {
						abstractRecordsToEntries.remove(b);
						entryB = entryB.unify(this, abstractRecordsToEntries.get(rep));
					}
					abstractRecordsToEntries.put(rep, entryA.unify(this, entryB));
				} catch (UnificationException e) {
					Optional<Issue> optionalIssue = backtrack(e.getIssue());
					if (optionalIssue.isPresent()) {
						return optionalIssue;
					}
					continue;
				}
				continue;
			}
			if (a instanceof AbstractRecordType) {
				// swap a and b
				AbstractRecordType tmp = abstractRecordGroups.find((AbstractRecordType) a);
				a = b;
				b = tmp;
			}
			if (b instanceof AbstractRecordType) {
				b = abstractRecordGroups.find((AbstractRecordType) b);
			}
			if (a.equals(b)) {
				// nothing to do
				continue;
			}
			if (a instanceof TypeVariable) {
				if (!a.equals(groupRepresentative)) {
					throw new InternalCompilerError();
				}
				// prevent infinite types
				if (b instanceof AbstractRecordType) {
					if (abstractRecordsToEntries.containsKey(b) &&
							abstractRecordsToEntries.get(b).hasVariable((TypeVariable) a)) {
						Optional<Issue> optionalIssue = backtrack(new InfiniteTypeIssue(a, b));
						if (optionalIssue.isPresent()) {
							return optionalIssue;
						}
						continue;
					}
				} else {
					if (b.accept(new TypeHasVariableVisitor((TypeVariable) a))) {
						Optional<Issue> optionalIssue = backtrack(new InfiniteTypeIssue(a, b));
						if (optionalIssue.isPresent()) {
							return optionalIssue;
						}
						continue;
					}
				}
				// the constraint is of the form "a = some type"
				// first, unify the type to which a maps with b
				if (mapping.containsKey(a)) {
					constraints.addFirst(new MonomorphicConstraint(constraint, mapping.get(a), b));
				}
				// then, assign a to that type
				mapping.put(((TypeVariable) a), b);
				constraint.getOrigins().forEach(a::addOrigin);
			} else if (a instanceof RecordType && b instanceof AbstractRecordType) {
				try {
					abstractRecordsToEntries.put(
							(AbstractRecordType) b,
							abstractRecordsToEntries.getOrDefault(b, RecordTypeEntry.Abstract.EMPTY_ABSTRACT_RECORD)
									.unify(this, new RecordTypeEntry.Concrete((RecordType) a)));
				} catch (UnificationException e) {
					Optional<Issue> optionalIssue = backtrack(e.getIssue());
					if (optionalIssue.isPresent()) {
						return optionalIssue;
					}
					continue;
				}
			} else if (a instanceof RecordType && b instanceof RecordType) {
				try {
					(new RecordTypeEntry.Concrete((RecordType) a))
							.unify(this, new RecordTypeEntry.Concrete((RecordType) b));
				} catch (UnificationException e) {
					Optional<Issue> optionalIssue = backtrack(e.getIssue());
					if (optionalIssue.isPresent()) {
						return optionalIssue;
					}
					continue;
				}
			} else if (a instanceof ArchetypeResourceType && b instanceof ArchetypeResourceType) {
				constraints.addFirst(new MonomorphicConstraint(
						constraint,
						((ArchetypeResourceType) a).getReadType(),
						((ArchetypeResourceType) b).getReadType()));
				constraints.addFirst(new MonomorphicConstraint(
						constraint,
						((ArchetypeResourceType) a).getWriteType(),
						((ArchetypeResourceType) b).getWriteType()));
			} else if (a instanceof ArchetypeResourceCollectionType && b instanceof ArchetypeResourceCollectionType) {
				constraints.addFirst(new MonomorphicConstraint(
						constraint,
						((ArchetypeResourceCollectionType) a).getKeyType(),
						((ArchetypeResourceCollectionType) b).getKeyType()));
				constraints.addFirst(new MonomorphicConstraint(
						constraint,
						((ArchetypeResourceCollectionType) a).getReadType(),
						((ArchetypeResourceCollectionType) b).getReadType()));
				constraints.addFirst(new MonomorphicConstraint(
						constraint,
						((ArchetypeResourceCollectionType) a).getWriteType(),
						((ArchetypeResourceCollectionType) b).getWriteType()));
			} else if (a instanceof SimpleContainerType && b instanceof SimpleContainerType) {
				// a simple container is a container with a single element type, e.g. Set[a], Slice[a], etc.
				// in order for SimpleContainer[a] = SimpleContainer[b],
				//   (1) the container types must be the same, and
				if (!a.getClass().equals(b.getClass())) {
					Optional<Issue> optionalIssue = backtrack(new UnsatisfiableConstraintIssue(a, b));
					if (optionalIssue.isPresent()) {
						return optionalIssue;
					}
					continue;
				}
				//   (2) the element types must be the same
				constraints.addFirst(new MonomorphicConstraint(
						constraint,
						((SimpleContainerType) a).getElementType(),
						((SimpleContainerType) b).getElementType()));
			} else if (a instanceof MapType && b instanceof MapType) {
				// for two map types to be the same,
				//   (1) the key types must be the same, and
				constraints.addFirst(new MonomorphicConstraint(
						constraint,
						((MapType) a).getKeyType(),
						((MapType) b).getKeyType()));
				//   (2) the value types must be the same
				constraints.addFirst(new MonomorphicConstraint(
						constraint,
						((MapType) a).getValueType(),
						((MapType) b).getValueType()));
			} else if (a instanceof TupleType && b instanceof TupleType) {
				// for two tuple types to be the same,
				TupleType ta = (TupleType) a;
				TupleType tb = (TupleType) b;
				//   (1) they must have the same number of element types
				if (ta.getElementTypes().size() != tb.getElementTypes().size()) {
					Optional<Issue> optionalIssue = backtrack(new UnsatisfiableConstraintIssue(a, b));
					if (optionalIssue.isPresent()) {
						return optionalIssue;
					}
					continue;
				}
				//   (2) each pair of corresponding element types must be the same
				for (int i = 0; i < ta.getElementTypes().size(); i++) {
					constraints.addFirst(new MonomorphicConstraint(
							constraint,
							ta.getElementTypes().get(i),
							tb.getElementTypes().get(i)));
				}
			} else if (a instanceof FunctionType && b instanceof FunctionType) {
				// in order for two function types to be the same,
				FunctionType fa = (FunctionType) a;
				FunctionType fb = (FunctionType) b;
				//   (1) their parameter lists must be of the same size, and
				if (fa.getParamTypes().size() != fb.getParamTypes().size()) {
					Optional<Issue> optionalIssue = backtrack(new UnsatisfiableConstraintIssue(a, b));
					if (optionalIssue.isPresent()) {
						return optionalIssue;
					}
					continue;
				}
				//   (2) each pair of corresponding parameter types must be the same, and
				for (int i = 0; i < fa.getParamTypes().size(); i++) {
					constraints.addFirst(new MonomorphicConstraint(
							constraint,
							fa.getParamTypes().get(i),
							fb.getParamTypes().get(i)));
				}
				//   (3) the return types must be the same
				constraints.addFirst(new MonomorphicConstraint(
						constraint,
						fa.getReturnType(),
						fb.getReturnType()));
			} else if (a instanceof ProcedureType && b instanceof ProcedureType) {
				// in order for two procedure types to be the same,
				ProcedureType pa = (ProcedureType) a;
				ProcedureType pb = (ProcedureType) b;
				//   (1) their parameter lists must be of the same size, and
				if (pa.getParamTypes().size() != pb.getParamTypes().size()) {
					Optional<Issue> optionalIssue = backtrack(new UnsatisfiableConstraintIssue(a, b));
					if (optionalIssue.isPresent()) {
						return optionalIssue;
					}
					continue;
				}
				//   (2) each pair of corresponding parameter types must be the same
				for (int i = 0; i < pa.getParamTypes().size(); i++) {
					constraints.addFirst(new MonomorphicConstraint(
							constraint,
							pa.getParamTypes().get(i),
							pb.getParamTypes().get(i)));
				}
			} else {
				Optional<Issue> optionalIssue = backtrack(new UnsatisfiableConstraintIssue(a, b));
				if (optionalIssue.isPresent()) {
					return optionalIssue;
				}
			}
			// we backtracked successfully, continue solving
		}
		return Optional.empty();
	}

	public void unify(IssueContext ctx) {
		Optional<Issue> issue = unify();
		if (issue.isPresent()) {
			ctx.error(issue.get());
			return;
		}
		simplify();
	}
}
