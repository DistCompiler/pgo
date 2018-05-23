package pgo.model.type;

import java.util.*;
import java.util.function.Consumer;

import pgo.errors.IssueContext;

/**
 * A constraint solver for PGo's type system. It does not support recursive types.
 */
public class PGoTypeSolver implements Consumer<PGoTypeConstraint> {
	private List<PGoTypeConstraint> constraints = new ArrayList<>();
	private HashMap<PGoTypeVariable, PGoType> mapping = new HashMap<>();

	public Map<PGoTypeVariable, PGoType> getMapping() {
		return Collections.unmodifiableMap(mapping);
	}

	public static Map<PGoTypeVariable, PGoType> unify(IssueContext ctx, PGoType... types) {
		if (types.length == 0) {
			return new HashMap<>();
		}
		PGoTypeSolver solver = new PGoTypeSolver();
		PGoType ty = types[0];
		for (PGoType t : types) {
			solver.accept(new PGoTypeConstraint(t, ty, t));
		}
		solver.unify(ctx);
		return solver.getMapping();
	}

	@Override
	public void accept(PGoTypeConstraint constraint) {
		constraints.add(constraint);
	}

	private void simplify() {
		boolean changed = true;
		while (changed) {
			changed = false;
			for (Map.Entry<PGoTypeVariable, PGoType> entry : mapping.entrySet()) {
				PGoTypeVariable k = entry.getKey();
				PGoType v = entry.getValue();
				PGoType newV = v.substitute(mapping).realize();
				if (!newV.equals(v)) {
					changed = true;
					mapping.put(k, newV);
				}
			}
		}
	}

	public void unify(IssueContext ctx) {
		while (constraints.size() != 0) {
			PGoTypeConstraint constraint = constraints.remove(constraints.size() - 1);
			// a and b are substituted so that we gain more information about their structures
			// a and b must not be null
			PGoType a = constraint.getLhs().substitute(mapping);
			PGoType b = constraint.getRhs().substitute(mapping);
			if (a.equals(b)) {
				// nothing to do
				continue;
			}
			if (a instanceof PGoTypeVariable && !b.contains((PGoTypeVariable) a)) {
				// the constraint is of the form "a = some type", so assign a to that type
				// the containment check prevents the occurrence of recursive types
				mapping.put(((PGoTypeVariable) a), b);
			} else if (b instanceof PGoTypeVariable && !a.contains((PGoTypeVariable) b)) {
				// the constraint is of the form "some type = b", so assign b to that type
				// the containment check prevents the occurrence of recursive types
				mapping.put(((PGoTypeVariable) b), a);
			} else if (a instanceof PGoTypeUnrealizedNumber && b instanceof PGoNumberType) {
				// attempt to promote the unrealized number a to the number b
				((PGoTypeUnrealizedNumber) a).harmonize((PGoNumberType) b);
			} else if (b instanceof PGoTypeUnrealizedNumber && a instanceof PGoNumberType) {
				// attempt to promote the unrealized number b to the number a
				((PGoTypeUnrealizedNumber) b).harmonize((PGoNumberType) a);
			} else if (a instanceof PGoSimpleContainerType && b instanceof PGoSimpleContainerType) {
				// a simple container is a container with a single element type, e.g. Set[a], Slice[a], etc.
				// in order for SimpleContainer[a] = SimpleContainer[b],
				//   (1) the container types must be the same, and
				if (!a.getClass().equals(b.getClass())) {
					ctx.error(new UnsatisfiableConstraintIssue(constraint, a, b));
					return;
				}
				//   (2) the element types must be the same
				accept(new PGoTypeConstraint(
						constraint,
						((PGoSimpleContainerType) a).getElementType(),
						((PGoSimpleContainerType) b).getElementType()));
			} else if (a instanceof PGoTypeMap && b instanceof PGoTypeMap) {
				// for two map types to be the same,
				//   (1) the key types must be the same, and
				accept(new PGoTypeConstraint(
						constraint,
						((PGoTypeMap) a).getKeyType(),
						((PGoTypeMap) b).getKeyType()));
				//   (2) the value types must be the same
				accept(new PGoTypeConstraint(
						constraint,
						((PGoTypeMap) a).getValueType(),
						((PGoTypeMap) b).getValueType()));
			} else if (a instanceof PGoTypeTuple && b instanceof PGoTypeTuple) {
				// for two tuple types to be the same,
				PGoTypeTuple ta = (PGoTypeTuple) a;
				PGoTypeTuple tb = (PGoTypeTuple) b;
				//   (1) they must have the same number of element types
				if (ta.getElementTypes().size() != tb.getElementTypes().size()) {
					ctx.error(new UnsatisfiableConstraintIssue(constraint, a, b));
					return;
				}
				//   (2) each pair of corresponding element types must be the same
				for (int i = 0; i < ta.getElementTypes().size(); i++) {
					accept(new PGoTypeConstraint(
							constraint,
							ta.getElementTypes().get(i),
							tb.getElementTypes().get(i)));
				}
			} else if (a instanceof PGoTypeUnrealizedTuple && b instanceof PGoSimpleContainerType) {
				// attempt to promote an unrealized tuple to a simple container type
				((PGoTypeUnrealizedTuple) a).harmonize(ctx, this, (PGoSimpleContainerType) b);
				if(ctx.hasErrors()) return;
			} else if (a instanceof PGoSimpleContainerType && b instanceof PGoTypeUnrealizedTuple) {
				((PGoTypeUnrealizedTuple) b).harmonize(ctx, this, (PGoSimpleContainerType) a);
				if(ctx.hasErrors()) return;
			} else if (a instanceof PGoTypeUnrealizedTuple && b instanceof PGoTypeTuple) {
				((PGoTypeUnrealizedTuple) a).harmonize(ctx, this, (PGoTypeTuple) b);
				if(ctx.hasErrors()) return;
			} else if (a instanceof PGoTypeTuple && b instanceof PGoTypeUnrealizedTuple) {
				((PGoTypeUnrealizedTuple) b).harmonize(ctx, this, (PGoTypeTuple) a);
				if(ctx.hasErrors()) return;
			} else if (a instanceof PGoTypeUnrealizedTuple && b instanceof PGoTypeUnrealizedTuple) {
				((PGoTypeUnrealizedTuple) a).harmonize(ctx, this, (PGoTypeUnrealizedTuple) b);
				if(ctx.hasErrors()) return;
			} else if (a instanceof PGoTypeFunction && b instanceof PGoTypeFunction) {
				// in order for two function types to be the same,
				PGoTypeFunction fa = (PGoTypeFunction) a;
				PGoTypeFunction fb = (PGoTypeFunction) b;
				//   (1) their parameter lists must be of the same size, and
				if (fa.getParamTypes().size() != fb.getParamTypes().size()) {
					ctx.error(new UnsatisfiableConstraintIssue(constraint, a, b));
					return;
				}
				//   (2) each pair of corresponding parameter types must be the same, and
				for (int i = 0; i < fa.getParamTypes().size(); i++) {
					accept(new PGoTypeConstraint(
							constraint,
							fa.getParamTypes().get(i),
							fb.getParamTypes().get(i)));
				}
				//   (3) the return types must be the same
				accept(new PGoTypeConstraint(
						constraint,
						fa.getReturnType(),
						fb.getReturnType()));
			} else {
				// there is no other case for type equality, hence, record error
				ctx.error(new UnsatisfiableConstraintIssue(constraint, a, b));
				return;
			}
		}
		simplify();
	}
}
