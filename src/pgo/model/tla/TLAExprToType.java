package pgo.model.tla;

import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoLibFunction;
import pgo.model.intermediate.PGoVariable;
import pgo.model.tla.PGoTLAExpression.PGoTLADefault;
import pgo.model.type.*;
import pgo.trans.PGoTransException;
import pgo.trans.PGoTransExpectedSingleExpressionException;
import pgo.trans.intermediate.PGoTempData;

import java.util.*;
import java.util.logging.Logger;
import java.util.stream.Collectors;

/**
 * Infer the Go type that a TLA AST expression evaluates to, and determine
 * whether the expression is legal in terms of typing, with the help of the
 * intermediate data.
 * 
 * This class is used both for type inference (in PGoTransStageType) and for
 * type checking (in PGoTransStageGoGen).
 *
 */
public class TLAExprToType {
	private PGoType type;
	// Contains typing information for variables
	private PGoTempData data;

	public TLAExprToType(PGoTLAExpression tla, PGoTempData data) throws PGoTransException {
		this.data = data;
		type = infer(tla);
	}

	public PGoType getType() {
		return type;
	}

	private PGoType infer(PGoTLAExpression tla) throws PGoTransException {
		PGoType t = tla.getType();
		if (t == null) {
			t = tla.inferType(this);
		}
		tla.setType(t);
		return t;
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
			return new TLAExprToType(tla.getContents().get(0), data).getType();
		}
		Map<Integer, PGoType> elements = new HashMap<>();
		List<PGoTLAExpression> contents = tla.getContents();
		for (int i = 0; i < contents.size(); i++) {
			PGoTLAExpression exp = contents.get(i);
			elements.put(i, new TLAExprToType(exp, data).getType());
		}
		return new PGoTypeUnrealizedTuple(elements);
	}

	protected PGoType type(PGoTLABool tla) {
		return PGoTypeBool.getInstance();
	}

	protected PGoType type(PGoTLABoolOp tla) throws PGoTransException {
		PGoType lhs = new TLAExprToType(tla.getLeft(), data).getType();
		PGoType rhs = new TLAExprToType(tla.getRight(), data).getType();
		PGoType fresh;

		// and/or take booleans only, and greater/less take numbers only
		switch (tla.getToken()) {
		case "/\\":
		case "\\land":
		case "\\/":
		case "\\lor":
			fresh = PGoTypeBool.getInstance();
			break;
		case "=<":
		case "\\leq":
		case "<=":
		case "\\geq":
		case ">=":
			fresh = new PGoTypeUnrealizedNumber();
			break;
		default:
			fresh = data.typeGenerator.get();
		}

		// The types on either side should be comparable.
		data.solver.accept(new PGoTypeConstraint(lhs, fresh, tla.getLine()));
		data.solver.accept(new PGoTypeConstraint(rhs, fresh, tla.getLine()));

		return PGoTypeBool.getInstance();
	}

	protected PGoType type(PGoTLAFunctionCall tla) throws PGoTransException {
		PGoType returnType = data.typeGenerator.get();
		List<PGoType> callParams = new ArrayList<>();
		for (PGoTLAExpression e : tla.getParams()) {
			callParams.add(new TLAExprToType(e, data).getType());
		}

		// TODO: change Head and Tail to a proper construct in the compiler
		if (tla.getName().equals("Head")){
			data.solver.accept(new PGoTypeConstraint(
					new PGoTypeFunction(callParams, returnType),
					new PGoTypeFunction(Collections.singletonList(new PGoTypeSlice(returnType)), returnType),
					tla.getLine()));
			return returnType;
		}
		if (tla.getName().equals("Tail")){
			data.solver.accept(new PGoTypeConstraint(
					new PGoTypeFunction(callParams, new PGoTypeSlice(returnType)),
					new PGoTypeFunction(
							Collections.singletonList(new PGoTypeSlice(returnType)),
							new PGoTypeSlice(returnType)),
					tla.getLine()));
			return new PGoTypeSlice(returnType);
		}

		// search for functions, TLA definitions, builtin funcs, tuples, slices,
		// or maps
		PGoFunction func = data.findPGoFunction(tla.getName());
		if (func != null) {
			// check params for type consistency
			List<PGoType> funcParams = func.getParams().stream().map(PGoVariable::getType).collect(Collectors.toList());
			data.solver.accept(new PGoTypeConstraint(
					new PGoTypeFunction(funcParams, func.getReturnType()),
					new PGoTypeFunction(callParams, func.getReturnType()),
					tla.getLine()));
			return func.getReturnType();
		}

		PGoTLADefinition def = data.findTLADefinition(tla.getName());
		if (def != null) {
			List<PGoType> funcParams = def.getParams().stream().map(PGoVariable::getType).collect(Collectors.toList());
			data.solver.accept(new PGoTypeConstraint(
					new PGoTypeFunction(funcParams, returnType),
					new PGoTypeFunction(callParams, returnType),
					tla.getLine()));
			PGoTempData temp = new PGoTempData(data);
			for (PGoVariable var : def.getParams()) {
				temp.getLocals().put(var.getName(), var);
			}
			data.solver.accept(new PGoTypeConstraint(
					new TLAExprToType(def.getExpr(), temp).getType(),
					returnType,
					tla.getLine()));
			return returnType;
		}

		PGoLibFunction lFunc = data.findBuiltInFunction(tla.getName());
		if (lFunc != null) {
			// see if a function exists w/ the given param types
			Optional<PGoLibFunction.LibFuncInfo> oFInfo = lFunc.getFunc(data.typeGenerator, callParams);
			if (oFInfo.isPresent()) {
				PGoLibFunction.LibFuncInfo fInfo = oFInfo.get();
				PGoTypeFunction funcType = fInfo.getFunctionType();
				data.solver.accept(new PGoTypeConstraint(
						new PGoTypeFunction(callParams, funcType.getReturnType()),
						funcType,
						tla.getLine()));
				return funcType.getReturnType();
			}
		}

		PGoVariable var = data.findPGoVariable(tla.getName());
		if (var == null) {
			throw new PGoTransException("No function or variable with the name " + tla.getName(), tla.getLine());
		}
		if (var.getType() instanceof PGoTypeTuple || var.getType() instanceof PGoTypeUnrealizedTuple) {
			if (tla.getParams().size() != 1) {
				throw new PGoTransException("Can't access multiple indices of tuple", tla.getLine());
			}
			PGoType type = new TLAExprToType(tla.getParams().get(0), data).getType();
			data.solver.accept(new PGoTypeConstraint(PGoTypeUnrealizedNumber.integralType(), type, tla.getLine()));
			// if the number is known at compile-time or the tuple is uniform, we can determine the type
			if (tla.getParams().get(0) instanceof PGoTLANumber) {
				int index = Integer.parseInt(((PGoTLANumber) tla.getParams().get(0)).getVal());
				if (var.getType() instanceof PGoTypeTuple) {
					List<PGoType> elementTypes = ((PGoTypeTuple) var.getType()).getElementTypes();
					if (index >= elementTypes.size()) {
						throw new PGoTransException(
								"Trying to access index " + index + " of tuple " + var.getType().toTypeName(),
								tla.getLine());
					}
					data.solver.accept(new PGoTypeConstraint(returnType, elementTypes.get(index), tla.getLine()));
					return returnType;
				}
				// unrealized tuple
				Map<Integer, PGoType> elementTypes = ((PGoTypeUnrealizedTuple) var.getType()).getElementTypes();
				if (elementTypes.containsKey(index)) {
					data.solver.accept(new PGoTypeConstraint(returnType, elementTypes.get(index), tla.getLine()));
					return returnType;
				}
				data.solver.accept(new PGoTypeConstraint(
						var.getType(),
						new PGoTypeUnrealizedTuple(Collections.singletonMap(index, returnType)),
						tla.getLine()));
				return returnType;
			} else {
				Logger.getGlobal().warning(
						"Can't determine the type of tuple element at compile-time (line " + tla.getLine() + ")");
				return returnType;
			}
		} else if (var.getType() instanceof PGoTypeSlice) {
			if (tla.getParams().size() != 1) {
				throw new PGoTransException("Can't access multiple indices of slice", tla.getLine());
			}
			PGoType type = new TLAExprToType(tla.getParams().get(0), data).getType();
			data.solver.accept(new PGoTypeConstraint(type, PGoTypeUnrealizedNumber.integralType(), tla.getLine()));
			return ((PGoTypeSlice) var.getType()).getElementType();
		} else if (var.getType() instanceof PGoTypeMap) {
			PGoType keyType = ((PGoTypeMap) var.getType()).getKeyType();
			if (tla.getParams().size() > 1) {
				List<PGoTLAExpression> params = tla.getParams();
				// something like f[1, 3] which is shorthand for f[<<1, 3>>]
				Map<Integer, PGoType> elementTypes = new HashMap<>();
				for (int i = 0; i < tla.getParams().size(); i++) {
					PGoType eltType = new TLAExprToType(tla.getParams().get(i), data).getType();
					elementTypes.put(i, eltType);
				}
				data.solver.accept(new PGoTypeConstraint(
						new PGoTypeUnrealizedTuple(elementTypes),
						keyType,
						tla.getLine()));
			} else {
				PGoType type = new TLAExprToType(tla.getParams().get(0), data).getType();
				data.solver.accept(new PGoTypeConstraint(type, keyType, tla.getLine()));
			}
			return ((PGoTypeMap) var.getType()).getValueType();
		}
		throw new PGoTransException("Can't access arbitrary elements of a " + var.getType().toTypeName(),
				tla.getLine());
	}

	protected PGoType type(PGoTLAGroup tla) throws PGoTransException {
		return new TLAExprToType(tla.getInner(), data).getType();
	}

	protected PGoType type(PGoTLANumber tla) {
		// TODO this check should probably be more sophisticated
		if (tla.getVal().contains(".")) {
			return new PGoTypeUnrealizedNumber(PGoTypeDecimal.getInstance());
		}
		return new PGoTypeUnrealizedNumber(PGoTypeInt.getInstance());
	}

	protected PGoType type(PGoTLASequence tla) throws PGoTransException {
		// the begin and end arguments should both be integers
		PGoType begin = new TLAExprToType(tla.getStart(), data).getType();
		PGoType end = new TLAExprToType(tla.getEnd(), data).getType();
		PGoType fresh = PGoTypeUnrealizedNumber.integralType();
		data.solver.accept(new PGoTypeConstraint(begin, fresh, tla.getLine()));
		data.solver.accept(new PGoTypeConstraint(end, fresh, tla.getLine()));
		return new PGoTypeSet(PGoTypeInt.getInstance());
	}

	protected PGoType type(PGoTLASet tla) throws PGoTransException {
		PGoTypeSet returnType = new PGoTypeSet(data.typeGenerator.get());
		if (tla.getContents().isEmpty()) {
			return returnType;
		}
		if (tla.getContents().get(0) instanceof PGoTLAVariadic) {
			// set constructor or set image
			if (tla.getContents().size() != 1) {
				throw new PGoTransExpectedSingleExpressionException(tla.getLine());
			}
			PGoTLAVariadic st = (PGoTLAVariadic) tla.getContents().get(0);
			data.solver.accept(new PGoTypeConstraint(
					new TLAExprToType(st, data).getType(),
					returnType.getElementType(),
					tla.getLine()));
			return returnType;
		}
		// elements are declared one by one
		// check if all elements are compatible and take the most specific type that works
		for (PGoTLAExpression elt : tla.getContents()) {
			data.solver.accept(new PGoTypeConstraint(
					new TLAExprToType(elt, data).getType(), returnType.getElementType(), tla.getLine()));
		}
		return returnType;
	}

	protected PGoType type(PGoTLASetOp tla) throws PGoTransException {
		switch (tla.getToken()) {
		case "\\in":
		case "\\notin":
			// the element type must be compatible w/ set type
			PGoType eltType = new TLAExprToType(tla.getLeft(), data).getType();
			PGoType setType = new TLAExprToType(tla.getRight(), data).getType();
			data.solver.accept(new PGoTypeConstraint(setType, new PGoTypeSet(eltType), tla.getLine()));
			return PGoTypeBool.getInstance();
		default:
			PGoType lhs = new TLAExprToType(tla.getLeft(), data).getType();
			PGoType rhs = new TLAExprToType(tla.getRight(), data).getType();
			setType = new PGoTypeSet(data.typeGenerator.get());
			data.solver.accept(new PGoTypeConstraint(lhs, setType, tla.getLine()));
			data.solver.accept(new PGoTypeConstraint(rhs, setType, tla.getLine()));
			if (tla.getToken().equals("\\subseteq")) {
				return PGoTypeBool.getInstance();
			}
			return setType;
		}
	}

	protected PGoType type(PGoTLASimpleArithmetic tla) throws PGoTransException {
		PGoType left = new TLAExprToType(tla.getLeft(), data).getType();
		PGoType right = new TLAExprToType(tla.getRight(), data).getType();
		PGoType result;
		switch (tla.getToken()) {
			case "\\div":
				result = PGoTypeUnrealizedNumber.integralType();
				data.solver.accept(new PGoTypeConstraint(left, result, tla.getLine()));
				data.solver.accept(new PGoTypeConstraint(right, result, tla.getLine()));
				break;
			case "/":
			case "^":
				result = new PGoTypeUnrealizedNumber(PGoTypeDecimal.getInstance());
				// PlusCal division is always floating-point (maybe? TLC can't check)
				// math.Pow returns float64
				data.solver.accept(new PGoTypeConstraint(left, result, tla.getLine()));
				data.solver.accept(new PGoTypeConstraint(right, result, tla.getLine()));
				break;
			default:
				result = new PGoTypeUnrealizedNumber();
				data.solver.accept(new PGoTypeConstraint(left, result, tla.getLine()));
				data.solver.accept(new PGoTypeConstraint(right, result, tla.getLine()));
				break;
		}
		return result;
	}

	protected PGoType type(PGoTLAString tla) {
		return PGoTypeString.getInstance();
	}

	protected PGoType type(PGoTLAUnary tla) throws PGoTransException {
		PGoType argType = new TLAExprToType(tla.getArg(), data).getType();
		PGoType fresh = data.typeGenerator.get();
		switch (tla.getToken()) {
		case "UNION":
			data.solver.accept(new PGoTypeConstraint(argType, new PGoTypeSet(new PGoTypeSet(fresh)), tla.getLine()));
			return new PGoTypeSet(fresh);
		case "SUBSET":
			data.solver.accept(new PGoTypeConstraint(argType, new PGoTypeSet(fresh), tla.getLine()));
			return new PGoTypeSet(new PGoTypeSet(fresh));
		case "~":
		case "\\lnot":
		case "\\neg":
			data.solver.accept(new PGoTypeConstraint(argType, PGoTypeBool.getInstance(), tla.getLine()));
		case "\\A":
		case "\\E":
			return PGoTypeBool.getInstance();
		case "CHOOSE":
			// CHOOSE x \in S : P(x)
			if (!(tla.getArg() instanceof PGoTLAVariadic)) {
				throw new PGoTransException("Expected a variadic expression", tla.getLine());
			}
			return argType;
		default:
			throw new PGoTransException("Unsupported unary operator", tla.getLine());
		}
	}

	protected PGoType type(PGoTLAVariable tla) {
		PGoVariable var = data.findPGoVariable(tla.getName());
		return (var == null ? data.typeGenerator.get() : var.getType());
	}

	// The returned type is never used in the context of the forall or exists
	// operations, since these always return bools. When the method is called in
	// this context, it is used only to check type consistency.
	protected PGoType type(PGoTLAVariadic tla) throws PGoTransException {
		switch (tla.getToken()) {
			case ":":
				PGoTempData temp = new PGoTempData(data);
				// Add typing data for variables local to this scope (the x \in S)
				for (PGoTLAExpression arg : tla.getArgs()) {
					// TODO handle stuff like << x, y >> \in S \X T
					PGoTLASetOp set = (PGoTLASetOp) arg;
					if (!(set.getLeft() instanceof PGoTLAVariable)) {
						throw new PGoTransException("Expected a variable", tla.getLine());
					}
					PGoTLAVariable var = (PGoTLAVariable) set.getLeft();
					PGoType containerType = new TLAExprToType(set.getRight(), data).getType();
					PGoType fresh = data.typeGenerator.get();
					data.solver.accept(new PGoTypeConstraint(containerType, new PGoTypeSet(fresh), tla.getLine()));
					temp.getLocals().put(var.getName(), PGoVariable.convert(var.getName(), fresh));
				}
				// Check if the expression agrees w/ types of variables
				PGoType exprType = new TLAExprToType(tla.getExpr(), temp).getType();
				if (tla.isRightSide()) {
					// the type is the return type of the function
					return exprType;
				}
				// if there is 1 set, the type is the contained type of the set;
				// otherwise we don't care since this must be forall/exists
				List<PGoTLAExpression> sets = tla.getArgs();
				if (sets.size() > 1) {
					return data.typeGenerator.get();
				}
				// x \in S
				PGoTLAExpression set = ((PGoTLASetOp) sets.get(0)).getRight();
				PGoType setType = new TLAExprToType(set, data).getType();
				PGoType fresh = data.typeGenerator.get();
				data.solver.accept(new PGoTypeConstraint(setType, new PGoTypeSet(fresh), tla.getLine()));
				return fresh;
			case "|->":
				// x \in S, y \in T |-> f(x, y)
				List<PGoTLAExpression> lhs = tla.getArgs();
				Map<Integer, PGoType> tupTypes = new HashMap<>();
				// Add typing data for locals while also adding components to tuple
				temp = new PGoTempData(data);
				for (int i = 0; i < lhs.size(); i++) {
					PGoTLAExpression elt = lhs.get(i);
					if (!(elt instanceof PGoTLASetOp)) {
						throw new PGoTransException("Expected a set operation", tla.getLine());
					}
					PGoTLAExpression setExpr = ((PGoTLASetOp) elt).getRight();
					setType = new TLAExprToType(setExpr, data).getType();
					fresh = data.typeGenerator.get();
					data.solver.accept(new PGoTypeConstraint(setType, new PGoTypeSet(fresh), tla.getLine()));
					tupTypes.put(i, fresh);
					PGoTLAExpression varExpr = ((PGoTLASetOp) elt).getLeft();
					// TODO handle tuples
					if (!(varExpr instanceof PGoTLAVariable)) {
						throw new PGoTransException("Expected a variable", tla.getLine());
					}
					temp.getLocals().put(((PGoTLAVariable) varExpr).getName(),
							PGoVariable.convert(((PGoTLAVariable) varExpr).getName(), fresh));
				}
				PGoType keyType;
				if (tupTypes.size() > 1) {
					keyType = new PGoTypeUnrealizedTuple(tupTypes);
				} else {
					keyType = tupTypes.get(0);
				}
				PGoType valType = new TLAExprToType(tla.getExpr(), temp).getType();
				return new PGoTypeMap(keyType, valType);
			case "EXCEPT":
				// TODO
			default:
				throw new PGoTransException("Unknown variadic operator", tla.getLine());
		}
	}

	public PGoType type(PGoTLADefault tla) {
		return data.typeGenerator.get();
	}

}
