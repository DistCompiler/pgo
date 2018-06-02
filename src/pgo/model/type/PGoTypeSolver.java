package pgo.model.type;

import java.util.*;
import java.util.stream.Collectors;

import pgo.errors.Issue;
import pgo.errors.IssueContext;

/**
 * A constraint solver for PGo's type system. It does not support recursive types.
 */
public class PGoTypeSolver {
	private Deque<PGoTypeConstraint> constraints = new ArrayDeque<>();
	private Map<PGoTypeVariable, PGoType> mapping = new HashMap<>();
	private Deque<PGoTypeSolver> stateStack = new ArrayDeque<>();

	public Map<PGoTypeVariable, PGoType> getMapping() {
		return Collections.unmodifiableMap(mapping);
	}

	public void addConstraint(PGoTypeConstraint constraint) {
		constraints.addLast(constraint);
	}

	private boolean backtrack() {
		if (stateStack.size() <= 0) {
			// unsuccessful
			return false;
		}
		PGoTypeSolver old = stateStack.pop();
		constraints = old.constraints;
		mapping = old.mapping;
		stateStack = old.stateStack;
		return true;
	}

	private PGoTypeSolver copy() {
		PGoTypeSolver copy = new PGoTypeSolver();
		copy.stateStack = new ArrayDeque<>(stateStack);
		copy.constraints = constraints.stream()
				.map(PGoTypeConstraint::copy)
				.collect(Collectors.toCollection(ArrayDeque::new));
		copy.mapping = new HashMap<>(mapping);
		return copy;
	}

	private void simplify(IssueContext ctx) {
		boolean changed = true;
		while (changed) {
			changed = false;
			for (Map.Entry<PGoTypeVariable, PGoType> entry : mapping.entrySet()) {
				PGoTypeVariable k = entry.getKey();
				PGoType v = entry.getValue();
				PGoType newV = v.substitute(mapping).realize(ctx);
				if (!newV.equals(v)) {
					changed = true;
					mapping.put(k, newV);
				}
			}
		}
	}

	Optional<Issue> unify() {
		while (constraints.size() != 0) {
			PGoTypeConstraint constraint = constraints.removeFirst();
			PGoType a;
			PGoType b;
			if (constraint instanceof PGoTypeMonomorphicConstraint) {
				a = ((PGoTypeMonomorphicConstraint) constraint).getLhs();
				b = ((PGoTypeMonomorphicConstraint) constraint).getRhs();
			} else if (constraint instanceof PGoTypePolymorphicConstraint) {
				if (!((PGoTypePolymorphicConstraint) constraint).hasNext()) {
					return Optional.of(new BacktrackingFailureIssue((PGoTypePolymorphicConstraint) constraint));
				}
				// extract first constraints
				List<PGoTypeEqualityConstraint> equalityConstraints = ((PGoTypePolymorphicConstraint) constraint).next();
				// snapshot state if there are any constraints left
				if (((PGoTypePolymorphicConstraint) constraint).hasNext()) {
					// push copy with current constraint added at front
					PGoTypeSolver copy = copy();
					copy.constraints.addFirst(constraint.copy());
					stateStack.push(copy);
				}
				// add the first constraints
				for (PGoTypeEqualityConstraint equalityConstraint : equalityConstraints) {
					constraints.addFirst(new PGoTypeMonomorphicConstraint(constraint.getOrigins(), equalityConstraint));
				}
				// solve the newly added constraints
				continue;
			} else {
				throw new RuntimeException("unreachable");
			}
			// a and b are substituted so that we gain more information about their structures
			a = a.substitute(mapping);
			b = b.substitute(mapping);
			if (a.equals(b)) {
				// nothing to do
				continue;
			}
			if (a instanceof PGoTypeVariable && !b.contains((PGoTypeVariable) a)) {
				// the constraint is of the form "a = some type", so assign a to that type
				// the containment check prevents the occurrence of recursive types
				mapping.put(((PGoTypeVariable) a), b);
				constraint.getOrigins().forEach(a::addOrigin);
			} else if (b instanceof PGoTypeVariable && !a.contains((PGoTypeVariable) b)) {
				// the constraint is of the form "some type = b", so assign b to that type
				// the containment check prevents the occurrence of recursive types
				mapping.put(((PGoTypeVariable) b), a);
				constraint.getOrigins().forEach(b::addOrigin);
			} else if (a instanceof PGoTypeUnrealizedNumber && b instanceof PGoNumberType) {
				// attempt to promote the unrealized number a to the number b
				Optional<Issue> issue = ((PGoTypeUnrealizedNumber) a).harmonize((PGoNumberType) b);
				if (issue.isPresent() && !backtrack()) {
					return issue;
				}
				constraint.getOrigins().forEach(a::addOrigin);
				if (b instanceof PGoTypeUnrealizedNumber) {
					constraint.getOrigins().forEach(b::addOrigin);
				}
			} else if (b instanceof PGoTypeUnrealizedNumber && a instanceof PGoNumberType) {
				// attempt to promote the unrealized number b to the number a
				Optional<Issue> issue = ((PGoTypeUnrealizedNumber) b).harmonize((PGoNumberType) a);
				if (issue.isPresent() && !backtrack()) {
					return issue;
				}
				constraint.getOrigins().forEach(b::addOrigin);
			} else if (a instanceof PGoSimpleContainerType && b instanceof PGoSimpleContainerType) {
				// a simple container is a container with a single element type, e.g. Set[a], Slice[a], etc.
				// in order for SimpleContainer[a] = SimpleContainer[b],
				//   (1) the container types must be the same, and
				if (!a.getClass().equals(b.getClass()) && !backtrack()) {
					return Optional.of(new UnsatisfiableConstraintIssue(constraint, a, b));
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
				if (ta.getElementTypes().size() != tb.getElementTypes().size() && !backtrack()) {
					return Optional.of(new UnsatisfiableConstraintIssue(constraint, a, b));
				}
				//   (2) each pair of corresponding element types must be the same
				for (int i = 0; i < ta.getElementTypes().size(); i++) {
					constraints.addFirst(new PGoTypeMonomorphicConstraint(
							constraint,
							ta.getElementTypes().get(i),
							tb.getElementTypes().get(i)));
				}
			} else if (a instanceof PGoTypeUnrealizedTuple && b instanceof PGoSimpleContainerType) {
				// attempt to promote an unrealized tuple to a simple container type
				Optional<Issue> issue = ((PGoTypeUnrealizedTuple) a).harmonize(this, (PGoSimpleContainerType) b);
				if (issue.isPresent() && !backtrack()) {
					return issue;
				}
				constraint.getOrigins().forEach(a::addOrigin);
			} else if (a instanceof PGoSimpleContainerType && b instanceof PGoTypeUnrealizedTuple) {
				Optional<Issue> issue = ((PGoTypeUnrealizedTuple) b).harmonize(this, (PGoSimpleContainerType) a);
				if (issue.isPresent() && !backtrack()) {
					return issue;
				}
				constraint.getOrigins().forEach(b::addOrigin);
			} else if (a instanceof PGoTypeUnrealizedTuple && b instanceof PGoTypeTuple) {
				Optional<Issue> issue = ((PGoTypeUnrealizedTuple) a).harmonize(constraint, this, (PGoTypeTuple) b);
				if (issue.isPresent() && !backtrack()) {
					return issue;
				}
				constraint.getOrigins().forEach(a::addOrigin);
			} else if (a instanceof PGoTypeTuple && b instanceof PGoTypeUnrealizedTuple) {
				Optional<Issue> issue = ((PGoTypeUnrealizedTuple) b).harmonize(constraint, this, (PGoTypeTuple) a);
				if (issue.isPresent() && !backtrack()) {
					return issue;
				}
				constraint.getOrigins().forEach(b::addOrigin);
			} else if (a instanceof PGoTypeUnrealizedTuple && b instanceof PGoTypeUnrealizedTuple) {
				Optional<Issue> issue = ((PGoTypeUnrealizedTuple) a).harmonize(constraint, this, (PGoTypeUnrealizedTuple) b);
				if (issue.isPresent() && !backtrack()) {
					return issue;
				}
				constraint.getOrigins().forEach(a::addOrigin);
				constraint.getOrigins().forEach(b::addOrigin);
			} else if (a instanceof PGoTypeFunction && b instanceof PGoTypeFunction) {
				// in order for two function types to be the same,
				PGoTypeFunction fa = (PGoTypeFunction) a;
				PGoTypeFunction fb = (PGoTypeFunction) b;
				//   (1) their parameter lists must be of the same size, and
				if (fa.getParamTypes().size() != fb.getParamTypes().size()) {
					return Optional.of(new UnsatisfiableConstraintIssue(constraint, a, b));
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
					return Optional.of(new UnsatisfiableConstraintIssue(constraint, a, b));
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
				return Optional.of(new UnsatisfiableConstraintIssue(constraint, a, b));
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
		simplify(ctx);
	}
}
