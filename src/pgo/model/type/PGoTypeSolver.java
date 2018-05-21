package pgo.model.type;

import java.util.*;
import java.util.function.Consumer;

/**
 * A constraint solver for PGo's type system. It does not support recursive types.
 */
public class PGoTypeSolver implements Consumer<PGoTypeConstraint> {
	private List<PGoTypeConstraint> constraints = new ArrayList<>();
	private HashMap<PGoTypeVariable, PGoType> mapping = new HashMap<>();

	public Map<PGoTypeVariable, PGoType> getMapping() {
		return Collections.unmodifiableMap(mapping);
	}

	public static Map<PGoTypeVariable, PGoType> unify(int line, PGoType... types) {
		if (types.length == 0) {
			return new HashMap<>();
		}
		PGoTypeSolver solver = new PGoTypeSolver();
		PGoType ty = types[0];
		for (PGoType t : types) {
			solver.accept(new PGoTypeConstraint(ty, t, line));
		}
		solver.unify();
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

	public void unify() {
		while (constraints.size() != 0) {
			PGoTypeConstraint constraint = constraints.remove(constraints.size() - 1);
			// a and b must not be null
			PGoType a = constraint.getLhs().substitute(mapping);
			PGoType b = constraint.getRhs().substitute(mapping);
			if (a.equals(b)) {
				// nothing to do
				continue;
			}
			if (a instanceof PGoTypeVariable && !b.contains((PGoTypeVariable) a)) {
				mapping.put(((PGoTypeVariable) a), b);
			} else if (b instanceof PGoTypeVariable && !a.contains((PGoTypeVariable) b)) {
				mapping.put(((PGoTypeVariable) b), a);
			} else if (a instanceof PGoTypeUnrealizedNumber && b instanceof PGoNumberType) {
				((PGoTypeUnrealizedNumber) a).harmonize(constraint.getLine(), (PGoNumberType) b);
			} else if (b instanceof PGoTypeUnrealizedNumber && a instanceof PGoNumberType) {
				((PGoTypeUnrealizedNumber) b).harmonize(constraint.getLine(), (PGoNumberType) a);
			} else if (a instanceof PGoSimpleContainerType && b instanceof PGoSimpleContainerType) {
				if (!a.getClass().equals(b.getClass())) {
					throw new PGoTypeUnificationException(a, b, constraint.getLine());
				}
				accept(new PGoTypeConstraint(
						((PGoSimpleContainerType) a).getElementType(),
						((PGoSimpleContainerType) b).getElementType(),
						constraint.getLine()));
			} else if (a instanceof PGoTypeMap && b instanceof PGoTypeMap) {
				accept(new PGoTypeConstraint(
						((PGoTypeMap) a).getKeyType(),
						((PGoTypeMap) b).getKeyType(),
						constraint.getLine()));
				accept(new PGoTypeConstraint(
						((PGoTypeMap) a).getValueType(),
						((PGoTypeMap) b).getValueType(),
						constraint.getLine()));
			} else if (a instanceof PGoTypeTuple && b instanceof PGoTypeTuple) {
				PGoTypeTuple ta = (PGoTypeTuple) a;
				PGoTypeTuple tb = (PGoTypeTuple) b;
				if (ta.getElementTypes().size() != tb.getElementTypes().size()) {
					throw new PGoTypeUnificationException(ta, tb, constraint.getLine());
				}
				for (int i = 0; i < ta.getElementTypes().size(); i++) {
					accept(new PGoTypeConstraint(
							ta.getElementTypes().get(i),
							tb.getElementTypes().get(i),
							constraint.getLine()));
				}
			} else if (a instanceof PGoTypeUnrealizedTuple && b instanceof PGoSimpleContainerType) {
				((PGoTypeUnrealizedTuple) a).harmonize(constraint.getLine(), this, (PGoSimpleContainerType) b);
			} else if (a instanceof PGoSimpleContainerType && b instanceof PGoTypeUnrealizedTuple) {
				((PGoTypeUnrealizedTuple) b).harmonize(constraint.getLine(), this, (PGoSimpleContainerType) a);
			} else if (a instanceof PGoTypeUnrealizedTuple && b instanceof PGoTypeTuple) {
				((PGoTypeUnrealizedTuple) a).harmonize(constraint.getLine(), this, (PGoTypeTuple) b);
			} else if (a instanceof PGoTypeTuple && b instanceof PGoTypeUnrealizedTuple) {
				((PGoTypeUnrealizedTuple) b).harmonize(constraint.getLine(), this, (PGoTypeTuple) a);
			} else if (a instanceof PGoTypeUnrealizedTuple && b instanceof PGoTypeUnrealizedTuple) {
				((PGoTypeUnrealizedTuple) a).harmonize(constraint.getLine(), this, (PGoTypeUnrealizedTuple) b);
			} else if (a instanceof PGoTypeFunction && b instanceof PGoTypeFunction) {
				PGoTypeFunction fa = (PGoTypeFunction) a;
				PGoTypeFunction fb = (PGoTypeFunction) b;
				if (fa.getParamTypes().size() != fb.getParamTypes().size()) {
					throw new PGoTypeUnificationException(fa, fb, constraint.getLine());
				}
				for (int i = 0; i < fa.getParamTypes().size(); i++) {
					accept(new PGoTypeConstraint(
							fa.getParamTypes().get(i),
							fb.getParamTypes().get(i),
							constraint.getLine()));
				}
				accept(new PGoTypeConstraint(
						fa.getReturnType(),
						fb.getReturnType(),
						constraint.getLine()));
			} else {
				throw new PGoTypeUnificationException(a, b, constraint.getLine());
			}
		}
		simplify();
	}
}
