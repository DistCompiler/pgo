package pgo.model.type;

import pgo.InternalCompilerError;
import pgo.Unreachable;
import pgo.errors.Issue;
import pgo.errors.IssueContext;
import pgo.util.UnionFind;

import java.util.*;
import java.util.stream.Collectors;

/**
 * A constraint solver for PGo's type system. It does not support recursive types.
 */
public class PGoTypeSolver {
	private Deque<PGoTypeConstraint> constraints = new ArrayDeque<>();
	private Map<PGoTypeVariable, PGoType> mapping = new HashMap<>();
	private UnionFind<PGoTypeVariable> variableGroups = new UnionFind<>();
	private UnionFind<PGoTypeAbstractRecord> abstractRecordGroups = new UnionFind<>();
	private Map<PGoTypeAbstractRecord, RecordTypeEntry> abstractRecordsToEntries = new HashMap<>();
	private Deque<PGoTypeSolver> stateStack = new ArrayDeque<>();

	private PGoTypeVariableSubstitutionVisitor subs =
			new PGoTypeVariableSubstitutionVisitor(new PGoTypeSubstitution(variableGroups, mapping));

	public PGoTypeSubstitution getSubstitution() {
		return new PGoTypeSubstitution(variableGroups, mapping);
	}

	public void addConstraint(PGoTypeConstraint constraint) {
		constraints.addLast(constraint);
	}

	void addFirst(PGoTypeConstraint constraint) {
		constraints.addFirst(constraint);
	}

	private boolean backtrack() {
		if (stateStack.size() <= 0) {
			// unsuccessful
			return false;
		}
		PGoTypeSolver old = stateStack.pop();
		constraints = old.constraints;
		mapping = old.mapping;
		variableGroups = old.variableGroups;
		abstractRecordGroups = old.abstractRecordGroups;
		abstractRecordsToEntries = old.abstractRecordsToEntries;
		stateStack = old.stateStack;
		subs = new PGoTypeVariableSubstitutionVisitor(new PGoTypeSubstitution(variableGroups, mapping));
		return true;
	}

	private PGoTypeSolver copy() {
		PGoTypeSolver copy = new PGoTypeSolver();
		copy.stateStack = new ArrayDeque<>(stateStack);
		copy.constraints = constraints.stream()
				.map(PGoTypeConstraint::copy)
				.collect(Collectors.toCollection(ArrayDeque::new));
		copy.mapping = new HashMap<>();
		copy.variableGroups = variableGroups.copy();
		copy.abstractRecordGroups = abstractRecordGroups.copy();
		copy.abstractRecordsToEntries = new HashMap<>(abstractRecordsToEntries);
		PGoTypeCopyVisitor visitor = new PGoTypeCopyVisitor();
		mapping.forEach((k, v) -> copy.mapping.put(k, v.accept(visitor)));
		copy.subs = null;
		return copy;
	}

	private void simplify() {
		boolean changed = true;
		while (changed) {
			changed = false;
			for (Map.Entry<PGoTypeVariable, PGoType> entry : mapping.entrySet()) {
				PGoTypeVariable k = entry.getKey();
				PGoType v = entry.getValue();
				PGoType newV = v.accept(subs);
				if (newV instanceof PGoTypeAbstractRecord) {
					newV = abstractRecordsToEntries
							.get(abstractRecordGroups.find((PGoTypeAbstractRecord) newV))
							.toConcreteRecord();
				}
				if (!newV.equals(v)) {
					changed = true;
					mapping.put(k, newV);
				}
			}
		}
	}

	private Optional<Issue> unify() {
		while (constraints.size() != 0) {
			PGoTypeConstraint constraint = constraints.removeFirst();
			if (constraint instanceof PGoTypePolymorphicConstraint) {
				if (!((PGoTypePolymorphicConstraint) constraint).hasNext()) {
					return Optional.of(new BacktrackingFailureIssue((PGoTypePolymorphicConstraint) constraint));
				}
				// extract first constraints
				List<PGoTypeBasicConstraint> basicConstraints = ((PGoTypePolymorphicConstraint) constraint).next();
				// snapshot state if there are any constraints left
				if (((PGoTypePolymorphicConstraint) constraint).hasNext()) {
					// push copy with current constraint added at front
					PGoTypeSolver copy = copy();
					copy.constraints.addFirst(constraint.copy());
					stateStack.push(copy);
				}
				// add the first constraints
				for (PGoTypeBasicConstraint basicConstraint : basicConstraints) {
					constraints.addFirst(new PGoTypeMonomorphicConstraint(constraint.getOrigins(), basicConstraint));
				}
				// solve the newly added constraints
				continue;
			}
			if (!(constraint instanceof PGoTypeMonomorphicConstraint)) {
				throw new Unreachable();
			}
			PGoTypeBasicConstraint basicConstraint = ((PGoTypeMonomorphicConstraint) constraint).getBasicConstraint();
			if (basicConstraint instanceof PGoTypeHasFieldConstraint) {
				PGoTypeHasFieldConstraint hasFieldConstraint = (PGoTypeHasFieldConstraint) basicConstraint;
				PGoType expressionType = hasFieldConstraint.getExpressionType();
				String fieldName = hasFieldConstraint.getFieldName();
				PGoType fieldType = hasFieldConstraint.getFieldType();
				if (expressionType instanceof PGoTypeRecord) {
					if (((PGoTypeRecord) expressionType).getFields().stream().noneMatch(f -> {
						if (f.getName().equals(fieldName)) {
							addFirst(new PGoTypeMonomorphicConstraint(constraint, fieldType, f.getType()));
							return true;
						}
						return false;
					})) {
						if (backtrack()) {
							continue;
						}
						return Optional.of(new NoMatchingFieldIssue((PGoTypeRecord) expressionType, fieldName));
					}
					continue;
				}
				if (expressionType instanceof PGoTypeAbstractRecord) {
					PGoTypeAbstractRecord abstractRecord =
							abstractRecordGroups.find((PGoTypeAbstractRecord) expressionType);
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
							if (backtrack()) {
								continue;
							}
							return Optional.of(e.getIssue());
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
			if (!(basicConstraint instanceof PGoTypeEqualityConstraint)) {
				throw new InternalCompilerError();
			}
			PGoType a = ((PGoTypeEqualityConstraint) basicConstraint).getLhs();
			PGoType b = ((PGoTypeEqualityConstraint) basicConstraint).getRhs();
			if (a instanceof PGoTypeVariable && b instanceof PGoTypeVariable) {
				// find the variable groups to which a and b belong
				a = variableGroups.find((PGoTypeVariable) a);
				b = variableGroups.find((PGoTypeVariable) b);
				// get the previous types to which a and b maps
				PGoType subbedA = a.accept(subs);
				PGoType subbedB = b.accept(subs);
				// union the two groups to which a and b belong
				variableGroups.union((PGoTypeVariable) a, (PGoTypeVariable) b);
				// add constraints for the group representative
				PGoTypeVariable groupRepresentative = variableGroups.find((PGoTypeVariable) a);
				if (!a.equals(groupRepresentative)) {
					mapping.remove(a);
					constraints.addFirst(new PGoTypeMonomorphicConstraint(
							Collections.emptyList(), new PGoTypeEqualityConstraint(groupRepresentative, subbedA)));
				}
				if (!b.equals(groupRepresentative)) {
					mapping.remove(b);
					constraints.addFirst(new PGoTypeMonomorphicConstraint(
							Collections.emptyList(), new PGoTypeEqualityConstraint(groupRepresentative, subbedB)));
				}
				continue;
			}
			PGoTypeVariable groupRepresentative = null;
			if (a instanceof PGoTypeVariable) {
				// find the variable group to which a belongs
				groupRepresentative = variableGroups.find((PGoTypeVariable) a);
				a = groupRepresentative;
			}
			if (b instanceof PGoTypeVariable) {
				// find the variable group to which b belongs
				groupRepresentative = variableGroups.find((PGoTypeVariable) b);
				// swap a and b
				b = a;
				a = groupRepresentative;
			}
			// a and b are substituted so that we gain more information about their structures
			a = a.accept(subs);
			b = b.accept(subs);
			// resolve abstract records
			if (a instanceof PGoTypeAbstractRecord && b instanceof PGoTypeAbstractRecord) {
				// find the variable groups to which a and b belong
				a = abstractRecordGroups.find((PGoTypeAbstractRecord) a);
				b = abstractRecordGroups.find((PGoTypeAbstractRecord) b);
				// get the previous entries to which a and b maps
				RecordTypeEntry entryA = abstractRecordsToEntries.getOrDefault(
						a, RecordTypeEntry.Abstract.EMPTY_ABSTRACT_RECORD);
				RecordTypeEntry entryB = abstractRecordsToEntries.getOrDefault(
						b, RecordTypeEntry.Abstract.EMPTY_ABSTRACT_RECORD);
				// union the two groups to which a and b belong
				abstractRecordGroups.union((PGoTypeAbstractRecord) a, (PGoTypeAbstractRecord) b);
				// add constraints for the group representative
				try {
					PGoTypeAbstractRecord rep = abstractRecordGroups.find((PGoTypeAbstractRecord) a);
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
					if (backtrack()) {
						continue;
					}
					return Optional.of(e.getIssue());
				}
				continue;
			}
			if (a instanceof PGoTypeAbstractRecord) {
				// swap a and b
				PGoTypeAbstractRecord tmp = abstractRecordGroups.find((PGoTypeAbstractRecord) a);
				a = b;
				b = tmp;
			}
			if (b instanceof PGoTypeAbstractRecord) {
				b = abstractRecordGroups.find((PGoTypeAbstractRecord) b);
			}
			if (a.equals(b)) {
				// nothing to do
				continue;
			}
			if (a instanceof PGoTypeVariable) {
				if (!a.equals(groupRepresentative)) {
					throw new InternalCompilerError();
				}
				// prevent infinite types
				if (b instanceof PGoTypeAbstractRecord) {
					if (abstractRecordsToEntries.containsKey(b) &&
							abstractRecordsToEntries.get(b).hasVariable((PGoTypeVariable) a)) {
						if (backtrack()) {
							continue;
						}
						return Optional.of(new InfiniteTypeIssue(a, b));
					}
				} else {
					if (b.accept(new PGoTypeHasVariableVisitor((PGoTypeVariable) a))) {
						if (backtrack()) {
							continue;
						}
						return Optional.of(new InfiniteTypeIssue(a, b));
					}
				}
				// the constraint is of the form "a = some type"
				// first, unify the type to which a maps with b
				if (mapping.containsKey(a)) {
					constraints.addFirst(new PGoTypeMonomorphicConstraint(constraint, mapping.get(a), b));
				}
				// then, assign a to that type
				mapping.put(((PGoTypeVariable) a), b);
				constraint.getOrigins().forEach(a::addOrigin);
			} else if (a instanceof PGoTypeRecord && b instanceof PGoTypeAbstractRecord) {
				try {
					abstractRecordsToEntries.put(
							(PGoTypeAbstractRecord) b,
							abstractRecordsToEntries.getOrDefault(b, RecordTypeEntry.Abstract.EMPTY_ABSTRACT_RECORD)
									.unify(this, new RecordTypeEntry.Concrete((PGoTypeRecord) a)));
				} catch (UnificationException e) {
					if (backtrack()) {
                        continue;
					}
					return Optional.of(e.getIssue());
				}
			} else if (a instanceof PGoTypeRecord && b instanceof PGoTypeRecord) {
				try {
					(new RecordTypeEntry.Concrete((PGoTypeRecord) a))
							.unify(this, new RecordTypeEntry.Concrete((PGoTypeRecord) b));
				} catch (UnificationException e) {
					if (backtrack()) {
						continue;
					}
					return Optional.of(e.getIssue());
				}
			} else if (a instanceof PGoSimpleContainerType && b instanceof PGoSimpleContainerType) {
				// a simple container is a container with a single element type, e.g. Set[a], Slice[a], etc.
				// in order for SimpleContainer[a] = SimpleContainer[b],
				//   (1) the container types must be the same, and
				if (!a.getClass().equals(b.getClass())) {
					if (backtrack()) {
						continue;
					}
					return Optional.of(new UnsatisfiableConstraintIssue(a, b));
				}
				//   (2) the element types must be the same
				constraints.addFirst(new PGoTypeMonomorphicConstraint(
						constraint,
						((PGoSimpleContainerType) a).getElementType(),
						((PGoSimpleContainerType) b).getElementType()));
			} else if (a instanceof PGoTypeMap && b instanceof PGoTypeMap) {
				// for two map types to be the same,
				//   (1) the key types must be the same, and
				constraints.addFirst(new PGoTypeMonomorphicConstraint(
						constraint,
						((PGoTypeMap) a).getKeyType(),
						((PGoTypeMap) b).getKeyType()));
				//   (2) the value types must be the same
				constraints.addFirst(new PGoTypeMonomorphicConstraint(
						constraint,
						((PGoTypeMap) a).getValueType(),
						((PGoTypeMap) b).getValueType()));
			} else if (a instanceof PGoTypeTuple && b instanceof PGoTypeTuple) {
				// for two tuple types to be the same,
				PGoTypeTuple ta = (PGoTypeTuple) a;
				PGoTypeTuple tb = (PGoTypeTuple) b;
				//   (1) they must have the same number of element types
				if (ta.getElementTypes().size() != tb.getElementTypes().size()) {
					if (backtrack()) {
						continue;
					}
					return Optional.of(new UnsatisfiableConstraintIssue(a, b));
				}
				//   (2) each pair of corresponding element types must be the same
				for (int i = 0; i < ta.getElementTypes().size(); i++) {
					constraints.addFirst(new PGoTypeMonomorphicConstraint(
							constraint,
							ta.getElementTypes().get(i),
							tb.getElementTypes().get(i)));
				}
			} else if (a instanceof PGoTypeFunction && b instanceof PGoTypeFunction) {
				// in order for two function types to be the same,
				PGoTypeFunction fa = (PGoTypeFunction) a;
				PGoTypeFunction fb = (PGoTypeFunction) b;
				//   (1) their parameter lists must be of the same size, and
				if (fa.getParamTypes().size() != fb.getParamTypes().size()) {
					if (backtrack()) {
						continue;
					}
					return Optional.of(new UnsatisfiableConstraintIssue(a, b));
				}
				//   (2) each pair of corresponding parameter types must be the same, and
				for (int i = 0; i < fa.getParamTypes().size(); i++) {
					constraints.addFirst(new PGoTypeMonomorphicConstraint(
							constraint,
							fa.getParamTypes().get(i),
							fb.getParamTypes().get(i)));
				}
				//   (3) the return types must be the same
				constraints.addFirst(new PGoTypeMonomorphicConstraint(
						constraint,
						fa.getReturnType(),
						fb.getReturnType()));
			} else if (a instanceof PGoTypeProcedure && b instanceof PGoTypeProcedure) {
				// in order for two procedure types to be the same,
				PGoTypeProcedure pa = (PGoTypeProcedure) a;
				PGoTypeProcedure pb = (PGoTypeProcedure) b;
				//   (1) their parameter lists must be of the same size, and
				if (pa.getParamTypes().size() != pb.getParamTypes().size()) {
					if (backtrack()) {
						continue;
					}
					return Optional.of(new UnsatisfiableConstraintIssue(a, b));
				}
				//   (2) each pair of corresponding parameter types must be the same
				for (int i = 0; i < pa.getParamTypes().size(); i++) {
					constraints.addFirst(new PGoTypeMonomorphicConstraint(
							constraint,
							pa.getParamTypes().get(i),
							pb.getParamTypes().get(i)));
				}
			} else if (!backtrack()) {
				// there is no other case for type equality, hence, record error
				return Optional.of(new UnsatisfiableConstraintIssue(a, b));
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
