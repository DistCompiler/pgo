package pgo.model.tla;

import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.golang.FunctionCall;
import pgo.model.golang.Group;
import pgo.model.golang.ParameterDeclaration;
import pgo.model.golang.Return;
import pgo.model.golang.SimpleExpression;
import pgo.model.golang.Statement;
import pgo.model.golang.Token;
import pgo.model.intermediate.PGoCollectionType;
import pgo.model.intermediate.PGoType;
import pgo.model.intermediate.PGoVariable;
import pgo.model.intermediate.PGoCollectionType.PGoSet;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.trans.PGoTransException;
import pgo.trans.intermediate.PGoTempData;
import pgo.trans.intermediate.PGoTransIntermediateData;

/**
 * Infer the Go type that a TLA expression evaluates to with the help of the
 * intermediate data.
 *
 */
public class TLAExprToType {
	private PGoType type;
	// Contains typing information for variables
	private PGoTransIntermediateData data;

	public TLAExprToType(PGoTLA tla, PGoTransIntermediateData data) throws PGoTransException {
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
	 * - Interface is compatible with all primitives, but not containers
	 * since this would create complications.
	 * 
	 * @return null if the types are not compatible
	 */
	private PGoType compatibleType(PGoType first, PGoType second) {
		if (first.equals(second)) {
			return first;
		}

		if (numberType.containsKey(first.toTypeName()) && numberType.containsKey(second.toTypeName())) {
			int firstPrec = numberType.get(first.toTypeName()), secondPrec = numberType.get(second.toTypeName());
			return (firstPrec > secondPrec ? first : second);
		}

		if (first instanceof PGoPrimitiveType && second instanceof PGoPrimitiveType) {
			if (first.equals(PGoType.inferFromGoTypeName("interface"))) {
				return second;
			}
		} else if (second.equals(PGoType.inferFromGoTypeName("interface"))) {
			return first;
		}

		// containers
		if (first instanceof PGoCollectionType && second instanceof PGoCollectionType) {

			if (first instanceof PGoSet && second instanceof PGoSet) {
				if (first.equals(PGoCollectionType.EMPTY_SET)) {
					return second;
				} else if (second.equals(PGoCollectionType.EMPTY_SET)) {
					return first;
				}

				return compatibleType(((PGoSet) first).getElementType(), ((PGoSet) second).getElementType());
			} else if (first.getClass().equals(second.getClass())) {
				return compatibleType(((PGoCollectionType) first).getElementType(),
						((PGoCollectionType) second).getElementType());
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

	protected PGoType type(PGoTLABoolOp tla) {
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

	protected PGoType type(PGoTLASequence tla) {
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
		case "\\subseteq":
			return PGoType.inferFromGoTypeName("bool");
		default:
			PGoType lhs = new TLAExprToType(tla.getLeft(), data).getType();
			PGoType rhs = new TLAExprToType(tla.getRight(), data).getType();
			PGoType result = compatibleType(lhs, rhs);
			if (result == null || !(result instanceof PGoSet)) {
				throw new PGoTransException("Can't use operator " + tla.getToken() + " on types " + lhs.toTypeName()
						+ " and " + rhs.toTypeName() + " (line " + tla.getLine() + ")");
			}
			return result;
		}
	}

	protected PGoType type(PGoTLASimpleArithmetic tla) throws PGoTransException {
		PGoType left = new TLAExprToType(tla.getLeft(), data).getType();
		PGoType right = new TLAExprToType(tla.getRight(), data).getType();

		PGoType result = compatibleType(left, right);
		if (result == null || !numberType.containsKey(result.toTypeName())) {
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
		switch (tla.getToken()) {
		case "UNION":
			PGoType setType = new TLAExprToType(tla.getArg(), data).getType();
			if (!(setType instanceof PGoSet)) {
				throw new PGoTransException("Can't UNION a " + setType.toTypeName() + " (line " + tla.getLine() + ")");
			}
			return PGoType.inferFromGoTypeName(((PGoSet) setType).getElementType().toTypeName());
		case "SUBSET":
			PGoType eltType = new TLAExprToType(tla.getArg(), data).getType();
			return PGoType.inferFromGoTypeName("set[" + eltType.toTypeName() + "]");
		case "~":
		case "\\lnot":
		case "\\neg":
		case "\\A":
		case "\\E":
			return PGoType.inferFromGoTypeName("bool");
		case "CHOOSE":
			// CHOOSE x \in S : P(x)
			assert (tla.getArg() instanceof PGoTLASuchThat);
			return new TLAExprToType(tla.getArg(), data).getType();
		default:
			assert false;
			return null;
		}
	}

	protected PGoType type(PGoTLAVariable tla) {
		return data.findPGoVariable(tla.getName()).getType();
	}

	// This method is never called in the context of the forall or exists
	// operations, since these always return bools.
	protected PGoType type(PGoTLASuchThat tla) throws PGoTransException {
		if (tla.isSetImage()) {
			// the type is the return type of the function
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

			return new TLAExprToType(tla.getExpr(), temp).getType();
		} else {
			// the type is the contained type of the set; only 1 set
			Vector<PGoTLASetOp> sets = tla.getSets();
			assert (sets.size() == 1);
			// x \in S
			PGoTLA set = sets.get(0).getRight();
			PGoType setType = new TLAExprToType(set, data).getType();
			assert (setType instanceof PGoSet);
			return ((PGoSet) setType).getElementType();
		}
	}
}
