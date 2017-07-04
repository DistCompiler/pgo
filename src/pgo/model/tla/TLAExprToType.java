package pgo.model.tla;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Vector;
import java.util.logging.Logger;

import pgo.model.intermediate.PGoCollectionType;
import pgo.model.intermediate.PGoType;
import pgo.model.intermediate.PGoVariable;
import pgo.model.intermediate.PGoCollectionType.PGoChan;
import pgo.model.intermediate.PGoCollectionType.PGoMap;
import pgo.model.intermediate.PGoCollectionType.PGoSet;
import pgo.model.intermediate.PGoCollectionType.PGoSlice;
import pgo.model.intermediate.PGoCollectionType.PGoTuple;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoLibFunction;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoPrimitiveType.PGoInt;
import pgo.model.intermediate.PGoPrimitiveType.PGoNatural;
import pgo.model.intermediate.PGoPrimitiveType.PGoNumber;
import pgo.model.intermediate.PGoPrimitiveType.PGoTemplateArgument;
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
	// The variable that this is assigned to, if relevant (when dealing w/
	// arrays)
	private PGoVariable assign;

	public TLAExprToType(PGoTLA tla, PGoTempData data) throws PGoTransException {
		this.data = data;
		this.assign = null;
		type = infer(tla);
	}

	public TLAExprToType(PGoTLA tla, PGoTempData data, PGoVariable assign) throws PGoTransException {
		this.data = data;
		this.assign = assign;
		type = infer(tla);
	}

	// The type is assign's type.
	public TLAExprToType(PGoTLA tla, PGoTempData data, PGoType assign) throws PGoTransException {
		this.data = data;
		if (assign != null) {
			this.assign = PGoVariable.convert("", assign);
		} else {
			this.assign = null;
		}
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
	 * - If a type is a template argument, the other type is returned.
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

		if (first instanceof PGoPrimitiveType.PGoTemplateArgument) {
			return second;
		}
		if (second instanceof PGoPrimitiveType.PGoTemplateArgument) {
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
			} else if (first instanceof PGoTuple && second instanceof PGoTuple) {
				// If a tuple contains a template arg, return the other.
				if (((PGoTuple) first).getLength() == -1 && ((PGoTuple) second).getLength() == -1) {
					if (!((PGoTuple) first).getType(0).equals(((PGoTuple) second).getType(0))) {
						return null;
					}
					return first;
				} else if (((PGoTuple) first).getLength() == -1 || ((PGoTuple) second).getLength() == -1) {
					return null;
				}
				Vector<PGoType> firstElts = ((PGoTuple) first).getContainedTypes(),
						secondElts = ((PGoTuple) second).getContainedTypes();
				// a single template argument is for the whole type
				if (firstElts.size() == 1 && firstElts.get(0) instanceof PGoTemplateArgument) {
					return second;
				}
				if (secondElts.size() == 1 && secondElts.get(0) instanceof PGoTemplateArgument) {
					return first;
				}
				if (firstElts.size() != secondElts.size()) {
					Logger.getGlobal().warning(
							"Comparing tuples of unequal lengths " + firstElts.size() + " and " + secondElts.size());
					// don't want to return null, since these are comparable
					return (first.isUndetermined() ? second : first);
				}
				Vector<PGoType> ret = new Vector<>();
				for (int i = 0; i < firstElts.size(); i++) {
					PGoType curElt = compatibleType(firstElts.get(i), secondElts.get(i));
					if (curElt == null) {
						return null;
					}
					ret.add(curElt);
				}
				return new PGoTuple(ret, false);
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
	protected PGoType type(PGoTLAArray tla) throws PGoTransException {
		if (!tla.getContents().isEmpty() && tla.getContents().get(0) instanceof PGoTLAVariadic) {
			// this is a map; typing is handled in the other method
			return new TLAExprToType(tla.getContents().get(0), data, assign).getType();
		}
		// We need to look at variable information to see if this is a tuple or
		// channel. By default we assume this is a tuple.
		if (assign == null) {
			// This is a tuple. Infer types of each element. If all types are
			// compatible, assume that the tuple is uniformly typed.
			Vector<String> containedTypes = new Vector<>();
			if (tla.getContents().isEmpty()) {
				return PGoType.inferFromGoTypeName("tuple[]");
			}
			PGoType first = new TLAExprToType(tla.getContents().get(0), data).getType();
			for (PGoTLA elt : tla.getContents()) {
				PGoType curType = new TLAExprToType(elt, data).getType();
				containedTypes.add(curType.toTypeName());
				first = TLAExprToType.compatibleType(first, curType);
			}
			if (first != null) {
				return PGoType.inferFromGoTypeName("tuple[" + first.toTypeName() + "...]");
			} else {
				return PGoType.inferFromGoTypeName("tuple[" + String.join(",", containedTypes) + "]");
			}
		} else if (assign.getType() instanceof PGoTuple) {
			// The type is the same as the assignment type. Check for
			// consistency.
			PGoTuple tup = (PGoTuple) assign.getType();
			if (tup.getLength() == -1) {
				PGoType contained = tup.getType(0);
				for (PGoTLA elt : tla.getContents()) {
					PGoType eltType = new TLAExprToType(elt, data, tup.getType(0)).getType();
					if (TLAExprToType.compatibleType(contained, eltType) == null) {
						throw new PGoTransException("Expected elements in tuple to be of type " + contained.toTypeName()
								+ " but found " + eltType.toTypeName() + " instead", tla.getLine());
					}
				}
			} else {
				if (tla.getContents().size() != tup.getLength()) {
					throw new PGoTransException("Expected type " + tup.toTypeName() + " to have "
							+ tup.getLength() + " elements, but found "
							+ tla.getContents().size() + " instead", tla.getLine());
				}
				for (int i = 0; i < tla.getContents().size(); i++) {
					PGoType eltType = new TLAExprToType(tla.getContents().get(i), data, tup.getType(i)).getType();
					if (TLAExprToType.compatibleType(tup.getType(i), eltType) == null) {
						throw new PGoTransException("Expected the " + i + "th component of the tuple "
								+ tup.toTypeName() + " to be of type " + tup.getType(i).toTypeName() + " but found "
								+ eltType.toTypeName() + " instead", tla.getLine());
					}
				}
			}
			return tup;
		} else if (assign.getType() instanceof PGoChan) {
			PGoType eltType = ((PGoChan) assign.getType()).getElementType();
			for (PGoTLA elt : tla.getContents()) {
				PGoType eType = new TLAExprToType(elt, data, eltType).getType();
				if (!eltType.equals(eType)) {
					throw new PGoTransException("Expected channel elements to be of type " + eltType.toTypeName()
							+ " but found " + eType.toTypeName(), tla.getLine());
				}
			}
			return assign.getType();
		} else if (assign.getType() instanceof PGoSlice) {
			PGoType eltType = ((PGoSlice) assign.getType()).getElementType();
			for (PGoTLA elt : tla.getContents()) {
				PGoType eType = new TLAExprToType(elt, data, eltType).getType();
				if (!eltType.equals(eType)) {
					throw new PGoTransException("Expected slice elements to be of type " + eltType.toTypeName()
							+ " but found " + eType.toTypeName(), tla.getLine());
				}
			}
			return assign.getType();
		}
		assert false;
		return null;
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
					+ lhs.toTypeName() + " and " + rhs.toTypeName(), tla.getLine());
		}
		// and/or take booleans only, and greater/less take numbers only
		switch (tla.getToken()) {
		case "/\\":
		case "\\land":
		case "\\/":
		case "\\lor":
			if (!lhs.equals(PGoType.inferFromGoTypeName("bool")) || !rhs.equals(PGoType.inferFromGoTypeName("bool"))) {
				throw new PGoTransException("The operator " + tla.getToken() + " cannot be used on the types "
						+ lhs.toTypeName() + " and " + rhs.toTypeName(), tla.getLine());
			}
			break;
		case "=<":
		case "\\leq":
		case "<=":
		case "\\geq":
		case ">=":
			if (!numberType.containsKey(lhs.toTypeName()) || !numberType.containsKey(rhs.toTypeName())) {
				throw new PGoTransException("The operator " + tla.getToken() + " cannot be used on the types "
						+ lhs.toTypeName() + " and " + rhs.toTypeName(), tla.getLine());
			}
			break;
		}
		return PGoType.inferFromGoTypeName("bool");
	}

	protected PGoType type(PGoTLAFunctionCall tla) throws PGoTransException {
		// search for functions, TLA definitions, builtin funcs, tuples, slices,
		// or maps
		PGoFunction func = data.findPGoFunction(tla.getName());
		if (func != null) {
			// check params for type consistency
			List<PGoVariable> funcParams = func.getParams();
			Vector<PGoTLA> callParams = tla.getParams();
			if (funcParams.size() != callParams.size()) {
				throw new PGoTransException("Expected function call " + tla.getName() + " to have " + funcParams.size()
						+ " parameters but found " + callParams.size() + " instead", tla.getLine());
			}

			for (int i = 0; i < funcParams.size(); i++) {
				PGoType paramType = new TLAExprToType(callParams.get(0), data).getType();
				if (!paramType.equals(funcParams.get(0).getType())) {
					throw new PGoTransException("Expected the " + i + "th parameter of the function " + tla.getName()
							+ " to be of type " + funcParams.get(0).getType().toTypeName() + " but found "
							+ paramType.toTypeName() + " instead", tla.getLine());
				}
			}
			return func.getReturnType();
		}

		PGoTLADefinition def = data.findTLADefinition(tla.getName());
		if (def != null) {
			Vector<PGoVariable> funcParams = def.getParams();
			Vector<PGoTLA> callParams = tla.getParams();
			if (funcParams.size() != callParams.size()) {
				throw new PGoTransException("Expected function call " + tla.getName() + " to have " + funcParams.size()
						+ " parameters but found " + callParams.size() + " instead", tla.getLine());
			}

			for (int i = 0; i < funcParams.size(); i++) {
				PGoType paramType = new TLAExprToType(callParams.get(0), data).getType();
				if (!paramType.equals(funcParams.get(0).getType())) {
					throw new PGoTransException("Expected the " + i + "th parameter of the function " + tla.getName()
							+ " to be of type " + funcParams.get(0).getType().toTypeName() + " but found "
							+ paramType.toTypeName() + " instead", tla.getLine());
				}
			}

			PGoTempData temp = new PGoTempData(data);
			for (PGoVariable var : funcParams) {
				temp.getLocals().put(var.getName(), var);
			}
			return new TLAExprToType(def.getExpr(), temp).getType();
		}

		PGoLibFunction lfunc = data.findBuiltInFunction(tla.getName());
		if (lfunc != null) {
			// see if a function exists w/ the given param types
			Vector<PGoType> callParams = new Vector<>();
			for (PGoTLA param : tla.getParams()) {
				callParams.add(new TLAExprToType(param, data).getType());
			}
			if (lfunc.getGoName(callParams) != null) {
				return lfunc.getRetType(callParams);
			}
		}

		PGoVariable var = data.findPGoVariable(tla.getName());
		if (var == null) {
			throw new PGoTransException("No function or variable with the name " + tla.getName(), tla.getLine());
		}
		if (var.getType() instanceof PGoTuple) {
			if (tla.getParams().size() != 1) {
				throw new PGoTransException("Can't access multiple indices of tuple", tla.getLine());
			}
			PGoType type = new TLAExprToType(tla.getParams().get(0), data).getType();
			if (!(type instanceof PGoNatural) && !(type instanceof PGoInt)) {
				throw new PGoTransException("Can't access non-integer tuple index", tla.getLine());
			}
			// if the number is known at compile-time or the tuple is uniform,
			// we can determine the type
			if (tla.getParams().get(0) instanceof PGoTLANumber) {
				return ((PGoTuple) var.getType())
						.getType(Integer.parseInt(((PGoTLANumber) tla.getParams().get(0)).getVal()));
			} else if (((PGoTuple) var.getType()).getLength() == -1) {
				return ((PGoTuple) var.getType()).getType(0);
			} else {
				Logger.getGlobal().warning(
						"Can't determine the type of tuple element at compile-time (line " + tla.getLine() + ")");
				return PGoType.UNDETERMINED;
			}
		} else if (var.getType() instanceof PGoSlice) {
			if (tla.getParams().size() != 1) {
				throw new PGoTransException("Can't access multiple indices of slice", tla.getLine());
			}
			PGoType type = new TLAExprToType(tla.getParams().get(0), data).getType();
			if (!(type instanceof PGoNatural) && !(type instanceof PGoInt)) {
				throw new PGoTransException("Can't access non-integer slice index", tla.getLine());
			}
			return ((PGoSlice) var.getType()).getElementType();
		} else if (var.getType() instanceof PGoMap) {
			PGoType keyType = ((PGoMap) var.getType()).getKeyType();
			if (tla.getParams().size() > 1) {
				// something like f[1, 3] which is shorthand for f[<<1, 3>>]
				if (!(keyType instanceof PGoTuple)) {
					throw new PGoTransException(
							"Can't use multiple indices to access map with key type " + keyType.toTypeName(),
							tla.getLine());
				}
				Vector<PGoType> tup = new Vector<>();
				for (int i = 0; i < tla.getParams().size(); i++) {
					tup.add(new TLAExprToType(tla.getParams().get(i), data, ((PGoTuple) keyType).getType(i)).getType());
				}
				PGoTuple key = new PGoTuple(tup, false);
				if (!key.equals(keyType)) {
					throw new PGoTransException("Can't use " + type.toTypeName() + " as key for "
							+ var.getType().toTypeName(), tla.getLine());
				}
			} else {
				PGoType type = new TLAExprToType(tla.getParams().get(0), data, keyType).getType();
				if (!type.equals(keyType)) {
					throw new PGoTransException("Can't use " + type.toTypeName() + " as key for "
							+ var.getType().toTypeName(), tla.getLine());
				}
			}
			return ((PGoMap) var.getType()).getElementType();
		}
		throw new PGoTransException(
				"Can't access arbitrary elements of a " + var.getType().toTypeName(), tla.getLine());
	}

	protected PGoType type(PGoTLAGroup tla) throws PGoTransException {
		return new TLAExprToType(tla.getInner(), data, assign).getType();
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
			throw new PGoTransException("The sequence operator \"..\" must take integers", tla.getLine());
		}
		return PGoType.inferFromGoTypeName("set[int]");
	}

	protected PGoType type(PGoTLASet tla) throws PGoTransException {
		if (tla.getContents().isEmpty()) {
			return PGoCollectionType.EMPTY_SET;
		}
		if (tla.getContents().get(0) instanceof PGoTLAVariadic) {
			// set constructor or set image
			assert (tla.getContents().size() == 1);
			PGoTLAVariadic st = (PGoTLAVariadic) tla.getContents().get(0);
			return PGoType.inferFromGoTypeName("set[" + new TLAExprToType(st, data).getType().toTypeName() + "]");
		} else {
			// check if an elt type is already available
			PGoType eltType = (assign == null ? null : ((PGoSet) assign.getType()).getElementType());
			// elt's are declared one by one
			PGoType first = new TLAExprToType(tla.getContents().get(0), data, eltType).getType();
			// check if all elts are compatible and take the most specific type
			// that works
			for (PGoTLA elt : tla.getContents()) {
				PGoType eType = new TLAExprToType(elt, data, eltType).getType();
				first = compatibleType(first, eType);
				if (first == null) {
					throw new PGoTransException(
							"Set initialized with elements of incompatible types", tla.getLine());
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
			PGoType setType = new TLAExprToType(tla.getRight(), data).getType();
			if (!(setType instanceof PGoSet)) {
				throw new PGoTransException("The right-hand argument of the " + tla.getToken()
						+ " operator must be a set", tla.getLine());
			}
			PGoType eltType = new TLAExprToType(tla.getLeft(), data, ((PGoSet) setType).getElementType()).getType();
			if (!setType.equals(PGoCollectionType.EMPTY_SET)
					&& compatibleType(eltType, ((PGoSet) setType).getElementType()) == null) {
				throw new PGoTransException(
						"The type " + eltType.toTypeName() + " is not compatible with the element type of the set "
								+ setType.toTypeName(),
						tla.getLine());
			}
			return PGoType.inferFromGoTypeName("bool");
		default:
			PGoType lhs = new TLAExprToType(tla.getLeft(), data, assign).getType();
			PGoType rhs = new TLAExprToType(tla.getRight(), data, assign).getType();
			PGoType result = compatibleType(lhs, rhs);
			if (result == null || !(result instanceof PGoSet)) {
				throw new PGoTransException("Can't use operator " + tla.getToken() + " on types " + lhs.toTypeName()
						+ " and " + rhs.toTypeName(), tla.getLine());
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
					+ left.toTypeName() + " and " + right.toTypeName(), tla.getLine());
		}

		if (tla.getToken().equals("\\div")) {
			if (numberType.get(left.toTypeName()) > numberType.get("int")
					|| numberType.get(right.toTypeName()) > numberType.get("int")) {
				throw new PGoTransException("Can't use integer division operator \"\\div\" on types "
						+ left.toTypeName() + " and " + right.toTypeName(), tla.getLine());
			}
		}

		// PlusCal division is always floating-point (maybe? TLC can't check)
		if (tla.getToken().equals("/") || tla.getToken().equals("^")) {
			// math.Pow returns float64
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
				throw new PGoTransException("Can't UNION a " + argType.toTypeName(), tla.getLine());
			}
			return PGoType.inferFromGoTypeName(((PGoSet) argType).getElementType().toTypeName());
		case "SUBSET":
			if (!(argType instanceof PGoSet)) {
				throw new PGoTransException("Can't take powerset of non-set type " + argType.toTypeName(),
						tla.getLine());
			}
			return PGoType.inferFromGoTypeName("set[" + argType.toTypeName() + "]");
		case "~":
		case "\\lnot":
		case "\\neg":
			if (!argType.equals(PGoType.inferFromGoTypeName("bool"))) {
				throw new PGoTransException("Can't negate a " + argType.toTypeName(), tla.getLine());
			}
		case "\\A":
		case "\\E":
			return PGoType.inferFromGoTypeName("bool");
		case "CHOOSE":
			// CHOOSE x \in S : P(x)
			assert (tla.getArg() instanceof PGoTLAVariadic);
			return argType;
		default:
			assert false;
			return null;
		}
	}

	protected PGoType type(PGoTLAVariable tla) {
		PGoVariable var = data.findPGoVariable(tla.getName());
		return (var == null ? PGoType.UNDETERMINED : var.getType());
	}

	// The returned type is never used in the context of the forall or exists
	// operations, since these always return bools. When the method is called in
	// this context, it is used only to check type consistency.
	protected PGoType type(PGoTLAVariadic tla) throws PGoTransException {
		switch (tla.getToken()) {
		case ":":
			PGoTempData temp = new PGoTempData(data);
			// Add typing data for variables local to this scope (the x \in S)
			for (PGoTLA arg : tla.getArgs()) {
				// TODO handle stuff like << x, y >> \in S \X T
				PGoTLASetOp set = (PGoTLASetOp) arg;
				assert (set.getLeft() instanceof PGoTLAVariable);
				PGoTLAVariable var = (PGoTLAVariable) set.getLeft();
				PGoType containerType = new TLAExprToType(set.getRight(), data).getType();
				assert (containerType instanceof PGoSet);
				PGoType eltType = ((PGoSet) containerType).getElementType();
				temp.getLocals().put(var.getName(), PGoVariable.convert(var.getName(), eltType));
			}
			// Check if the expression agrees w/ types of variables
			PGoType exprType = new TLAExprToType(tla.getExpr(), temp).getType();

			if (tla.isRightSide()) {
				// the type is the return type of the function
				return exprType;
			} else {
				// if there is 1 set, the type is the contained type of the set;
				// otherwise we don't care since this must be forall/exists
				Vector<PGoTLA> sets = tla.getArgs();
				if (sets.size() > 1) {
					return PGoType.UNDETERMINED;
				}
				// x \in S
				PGoTLA set = ((PGoTLASetOp) sets.get(0)).getRight();
				PGoType setType = new TLAExprToType(set, data).getType();
				assert (setType instanceof PGoSet);
				return ((PGoSet) setType).getElementType();
			}
		case "|->":
			// x \in S, y \in T |-> f(x, y)
			Vector<PGoTLA> lhs = tla.getArgs();
			Vector<PGoType> tupTypes = new Vector<>();
			// Add typing data for locals while also adding components to tuple
			temp = new PGoTempData(data);
			for (PGoTLA elt : lhs) {
				assert (elt instanceof PGoTLASetOp);
				PGoTLA setExpr = ((PGoTLASetOp) elt).getRight();
				PGoType setType = new TLAExprToType(setExpr, data).getType();
				assert (setType instanceof PGoSet);
				tupTypes.add(((PGoSet) setType).getElementType());

				PGoTLA varExpr = ((PGoTLASetOp) elt).getLeft();
				// TODO handle tuples
				assert (varExpr instanceof PGoTLAVariable);
				temp.getLocals().put(((PGoTLAVariable) varExpr).getName(),
						PGoVariable.convert(((PGoTLAVariable) varExpr).getName(), ((PGoSet) setType).getElementType()));
			}
			PGoType keyType;
			if (tupTypes.size() > 1) {
				keyType = new PGoTuple(tupTypes, false);
			} else {
				keyType = tupTypes.get(0);
			}
			PGoType valType = new TLAExprToType(tla.getExpr(), temp).getType();
			return PGoType.inferFromGoTypeName("map[" + keyType.toTypeName() + "]" + valType.toTypeName());
		case "EXCEPT":
			// TODO
		default:
			assert false;
			return null;
		}
	}
}
