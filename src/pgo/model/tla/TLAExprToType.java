package pgo.model.tla;

import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

import pgo.model.intermediate.PGoCollectionType;
import pgo.model.intermediate.PGoType;
import pgo.model.intermediate.PGoVariable;
import pgo.model.intermediate.PGoCollectionType.PGoChan;
import pgo.model.intermediate.PGoCollectionType.PGoMap;
import pgo.model.intermediate.PGoCollectionType.PGoSet;
import pgo.model.intermediate.PGoCollectionType.PGoSlice;
import pgo.model.intermediate.PGoPrimitiveType.PGoNumber;
import pgo.trans.PGoTransException;
import pgo.trans.intermediate.PGoTempData;

/**
 * Infer the Go type that a TLA expression evaluates to, and determine whether
 * the expression is legal in terms of typing, with the help of the intermediate
 * data.
 *
 */
public class TLAExprToType {
	private PGoType type;
	// Contains typing information for variables
	private PGoTempData data;

	public TLAExprToType(PGoTLA tla, PGoTempData data) throws PGoTransException {
		this.data = data;
		type = infer(tla);
	}

	public PGoType getType() {
		return type;
	}

	private PGoType infer(PGoTLA tla) throws PGoTransException {
		return tla.inferType(this);
	}

	/**
	 * Map the number type name to its specificity (precedence in promotion).
	 * Floating-point numbers have the highest precedence (most general type).
	 */
	private final static Map<String, Integer> numberType = new HashMap<String, Integer>() {
		{
			put("uint64", 1);
			put("int", 2);
			put("float64", 3);
		}
	};

	/**
	 * Determine whether two types are compatible, and return the most specific
	 * type that is compatible with both.
	 * - Arbitrary types are compatible if they are the same type.
	 * - All number types are compatible.
	 * - Sets and other containers are compatible if they are the same type
	 * of container and their contained types are compatible.
	 * - Interface is said to be not compatible with any type.
	 * - We don't care about pointers, anonymous functions, or void types since
	 * these don't appear in TLA expressions.
	 * 
	 * @return null if the types are not compatible, or if at least one type is
	 *         undetermined
	 */
	public static PGoType compatibleType(PGoType first, PGoType second) {
		if (first.equals(PGoType.UNDETERMINED) || second.equals(PGoType.UNDETERMINED)) {
			return null;
		}

		if (first.equals(second)) {
			return first;
		}

		if (first instanceof PGoNumber && second instanceof PGoNumber) {
			int firstPrec = numberType.get(first.toTypeName()), secondPrec = numberType.get(second.toTypeName());
			return (firstPrec > secondPrec ? first : second);
		}

		// containers
		if (first instanceof PGoCollectionType && second instanceof PGoCollectionType) {

			if (first instanceof PGoSet && second instanceof PGoSet) {
				if (first.equals(PGoCollectionType.EMPTY_SET)) {
					return second;
				} else if (second.equals(PGoCollectionType.EMPTY_SET)) {
					return first;
				}

				PGoType contained = compatibleType(((PGoSet) first).getElementType(),
						((PGoSet) second).getElementType());
				if (contained == null) {
					return null;
				}
				return PGoType.inferFromGoTypeName("set[" + contained.toTypeName() + "]");
			} else if (first.getClass().equals(second.getClass())) {
				PGoType contained = compatibleType(((PGoCollectionType) first).getElementType(),
						((PGoCollectionType) second).getElementType());
				if (contained == null) {
					return null;
				}

				if (first instanceof PGoSlice) {
					return PGoType.inferFromGoTypeName("[]" + contained.toTypeName());
				} else if (first instanceof PGoChan) {
					return PGoType.inferFromGoTypeName("chan[" + contained.toTypeName() + "]");
				} else if (first instanceof PGoMap) {
					PGoType key1 = ((PGoMap) first).getKeyType(), key2 = ((PGoMap) second).getKeyType();
					PGoType keyType = compatibleType(key1, key2);
					if (keyType == null) {
						return null;
					}
					return PGoType.inferFromGoTypeName("map[" + keyType.toTypeName() + "]" + contained.toTypeName());
				}
			}
		}
		return null;
	}

	/**
	 * Return the type that the TLA expression evaluates to.
	 * 
	 * @throws PGoTransException
	 *             if there is a type inconsistency
	 */
	protected PGoType type(PGoTLAArray tla) {
		// TODO
		return PGoType.UNDETERMINED;
	}

	protected PGoType type(PGoTLABool tla) {
		return PGoType.inferFromGoTypeName("bool");
	}

	protected PGoType type(PGoTLABoolOp tla) throws PGoTransException {
		// The types on either side should be comparable.
		PGoType lhs = new TLAExprToType(tla.getLeft(), data).getType();
		PGoType rhs = new TLAExprToType(tla.getRight(), data).getType();
		PGoType compar = compatibleType(lhs, rhs);
		if (compar == null) {
			throw new PGoTransException("The operator " + tla.getToken() + " cannot be used on the types "
					+ lhs.toTypeName() + " and " + rhs.toTypeName() + " (line " + tla.getLine() + ")");
		}
		// and/or take booleans only, and greater/less take numbers only
		switch (tla.getToken()) {
		case "/\\":
		case "\\land":
		case "\\/":
		case "\\lor":
			if (!lhs.equals(PGoType.inferFromGoTypeName("bool")) || !rhs.equals(PGoType.inferFromGoTypeName("bool"))) {
				throw new PGoTransException("The operator " + tla.getToken() + " cannot be used on the types "
						+ lhs.toTypeName() + " and " + rhs.toTypeName() + " (line " + tla.getLine() + ")");
			}
			break;
		case "=<":
		case "\\leq":
		case "<=":
		case "\\geq":
		case ">=":
			if (!numberType.containsKey(lhs.toTypeName()) || !numberType.containsKey(rhs.toTypeName())) {
				throw new PGoTransException("The operator " + tla.getToken() + " cannot be used on the types "
						+ lhs.toTypeName() + " and " + rhs.toTypeName() + " (line " + tla.getLine() + ")");
			}
			break;
		}
		return PGoType.inferFromGoTypeName("bool");
	}

	protected PGoType type(PGoTLAFunction tla) {
		// TODO
		return PGoType.UNDETERMINED;
	}

	protected PGoType type(PGoTLAGroup tla) throws PGoTransException {
		return new TLAExprToType(tla.getInner(), data).getType();
	}

	protected PGoType type(PGoTLANumber tla) {
		if (tla.getVal().contains(".")) {
			// TODO this check should probably be more sophisticated
			return PGoType.inferFromGoTypeName("float64");
		} else {
			return PGoType.inferFromGoTypeName("int");
		}
	}

	protected PGoType type(PGoTLASequence tla) throws PGoTransException {
		// the begin and end arguments should both be integers
		PGoType begin = new TLAExprToType(tla.getStart(), data).getType();
		PGoType end = new TLAExprToType(tla.getEnd(), data).getType();
		if (!(begin instanceof PGoNumber) || !(end instanceof PGoNumber)
				|| numberType.get(begin.toTypeName()) > numberType.get("int")
				|| numberType.get(end.toTypeName()) > numberType.get("int")) {
			throw new PGoTransException("The sequence operator \"..\" must take integers (line " + tla.getLine() + ")");
		}
		return PGoType.inferFromGoTypeName("[]int");
	}

	protected PGoType type(PGoTLASet tla) throws PGoTransException {
		if (tla.getContents().isEmpty()) {
			return PGoCollectionType.EMPTY_SET;
		}
		if (tla.getContents().get(0) instanceof PGoTLASuchThat) {
			// set constructor or set image
			assert (tla.getContents().size() == 1);
			PGoTLASuchThat st = (PGoTLASuchThat) tla.getContents().get(0);
			return PGoType.inferFromGoTypeName("set[" + new TLAExprToType(st, data).getType().toTypeName() + "]");
		} else {
			// elt's are declared one by one
			PGoType first = new TLAExprToType(tla.getContents().get(0), data).getType();
			// check if all elts are compatible and take the most specific type
			// that works
			for (PGoTLA elt : tla.getContents()) {
				PGoType eltType = new TLAExprToType(elt, data).getType();
				first = compatibleType(first, eltType);
				if (first == null) {
					throw new PGoTransException(
							"Set initialized with elements of incompatible types (line " + tla.getLine() + ")");
				}
			}
			return PGoType.inferFromGoTypeName("set[" + first.toTypeName() + "]");
		}
	}

	protected PGoType type(PGoTLASetOp tla) throws PGoTransException {
		switch (tla.getToken()) {
		case "\\in":
		case "\\notin":
			// the element type must be compatible w/ set type
			PGoType eltType = new TLAExprToType(tla.getLeft(), data).getType();
			PGoType setType = new TLAExprToType(tla.getRight(), data).getType();
			if (!(setType instanceof PGoSet)) {
				throw new PGoTransException("The right-hand argument of the " + tla.getToken()
						+ " operator must be a set (line " + tla.getLine() + ")");
			}
			if (!setType.equals(PGoCollectionType.EMPTY_SET)
					&& compatibleType(eltType, ((PGoSet) setType).getElementType()) == null) {
				throw new PGoTransException(
						"The type " + eltType.toTypeName() + " is not compatible with the element type of the set "
								+ setType.toTypeName() + " (line " + tla.getLine() + ")");
			}
			return PGoType.inferFromGoTypeName("bool");
		default:
			PGoType lhs = new TLAExprToType(tla.getLeft(), data).getType();
			PGoType rhs = new TLAExprToType(tla.getRight(), data).getType();
			PGoType result = compatibleType(lhs, rhs);
			if (result == null || !(result instanceof PGoSet)) {
				throw new PGoTransException("Can't use operator " + tla.getToken() + " on types " + lhs.toTypeName()
						+ " and " + rhs.toTypeName() + " (line " + tla.getLine() + ")");
			}
			if (tla.getToken().equals("\\subseteq")) {
				return PGoType.inferFromGoTypeName("bool");
			}
			return result;
		}
	}

	protected PGoType type(PGoTLASimpleArithmetic tla) throws PGoTransException {
		PGoType left = new TLAExprToType(tla.getLeft(), data).getType();
		PGoType right = new TLAExprToType(tla.getRight(), data).getType();

		PGoType result = compatibleType(left, right);
		if (!(result instanceof PGoNumber)) {
			throw new PGoTransException("Can't use arithmetic operator " + tla.getToken() + " on types "
					+ left.toTypeName() + " and " + right.toTypeName() + " (line " + tla.getLine() + ")");
		}

		// PlusCal division is always floating-point (maybe? TLC can't check)
		if (tla.getToken().equals("/")) {
			return PGoType.inferFromGoTypeName("float64");
		}
		return result;
	}

	protected PGoType type(PGoTLAString tla) {
		return PGoType.inferFromGoTypeName("string");
	}

	protected PGoType type(PGoTLAUnary tla) throws PGoTransException {
		PGoType argType = new TLAExprToType(tla.getArg(), data).getType();
		switch (tla.getToken()) {
		case "UNION":
			if (!(argType instanceof PGoSet) || !(((PGoSet) argType).getElementType() instanceof PGoSet)) {
				throw new PGoTransException("Can't UNION a " + argType.toTypeName() + " (line " + tla.getLine() + ")");
			}
			return PGoType.inferFromGoTypeName(((PGoSet) argType).getElementType().toTypeName());
		case "SUBSET":
			if (!(argType instanceof PGoSet)) {
				throw new PGoTransException("Can't take powerset of non-set type " + argType.toTypeName() + " (line "
						+ tla.getLine() + ")");
			}
			return PGoType.inferFromGoTypeName("set[" + argType.toTypeName() + "]");
		case "~":
		case "\\lnot":
		case "\\neg":
			if (!argType.equals(PGoType.inferFromGoTypeName("bool"))) {
				throw new PGoTransException("Can't negate a " + argType.toTypeName() + " (line " + tla.getLine() + ")");
			}
		case "\\A":
		case "\\E":
			return PGoType.inferFromGoTypeName("bool");
		case "CHOOSE":
			// CHOOSE x \in S : P(x)
			assert (tla.getArg() instanceof PGoTLASuchThat);
			return argType;
		default:
			assert false;
			return null;
		}
	}

	protected PGoType type(PGoTLAVariable tla) {
		return data.findPGoVariable(tla.getName()).getType();
	}

	// The returned type is never used in the context of the forall or exists
	// operations, since these always return bools. When the method is called in
	// this context, it is used only to check type consistency.
	protected PGoType type(PGoTLASuchThat tla) throws PGoTransException {

		PGoTempData temp = new PGoTempData(data);
		// Add typing data for variables local to this scope (the x \in S)
		for (PGoTLASetOp set : tla.getSets()) {
			// TODO handle stuff like << x, y >> \in S \X T
			assert (set.getLeft() instanceof PGoTLAVariable);
			PGoTLAVariable var = (PGoTLAVariable) set.getLeft();
			PGoType containerType = new TLAExprToType(set.getRight(), data).getType();
			assert (containerType instanceof PGoSet);
			PGoType eltType = ((PGoSet) containerType).getElementType();
			temp.getLocals().put(var.getName(), PGoVariable.convert(var.getName(), eltType));
		}
		// Check if the expression agrees w/ types of variables
		PGoType exprType = new TLAExprToType(tla.getExpr(), temp).getType();

		if (tla.isSetImage()) {
			// the type is the return type of the function
			return exprType;
		} else {
			// if there is 1 set, the type is the contained type of the set;
			// otherwise we don't care since this must be forall/exists
			Vector<PGoTLASetOp> sets = tla.getSets();
			if (sets.size() > 1) {
				return PGoType.UNDETERMINED;
			}
			// x \in S
			PGoTLA set = sets.get(0).getRight();
			PGoType setType = new TLAExprToType(set, data).getType();
			assert (setType instanceof PGoSet);
			return ((PGoSet) setType).getElementType();
		}
	}
}
