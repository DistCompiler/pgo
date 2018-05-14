package pgo.trans.intermediate;

import java.util.*;
import java.util.stream.Collectors;

import pcal.AST;
import pcal.AST.PVarDecl;
import pcal.AST.Process;
import pcal.AST.SingleAssign;
import pcal.AST.VarDecl;
import pcal.TLAExpr;
import pcal.TLAExprPgo;
import pgo.model.intermediate.*;
import pgo.model.parser.AnnotatedFunction;
import pgo.model.parser.AnnotatedProcess;
import pgo.model.parser.AnnotatedReturnVariable;
import pgo.model.parser.AnnotatedTLADefinition;
import pgo.model.parser.AnnotatedVariable;
import pgo.model.parser.AnnotatedVariable.VarAnnotatedVariable;
import pgo.model.tla.*;
import pgo.model.type.*;
import pgo.model.type.PGoType;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;
import pgo.trans.PGoTransExpectedSingleExpressionException;
import pgo.util.PGoTypeUtil;
import pgo.util.PcalASTUtil;

/**
 * The second stage of the translation where we determine the types of all
 * variables and functions of the algorithm. This stage should end with all
 * variables' and functions' types being completely determined, otherwise a
 * PGoTransException will be thrown.
 *
 */
public class PGoTransStageType {
	// intermediate data, which is filled with typing information from
	// annotations
	PGoTransIntermediateData data;

	public PGoTransStageType(PGoTransStageTLAParse s1) throws PGoTransException {
		this.data = s1.data;

		addAnnotatedDefinitions();
		applyAnnotationOnVariables();
		applyAnnotationOnFunctions();
		applyAnnotationOnReturnVariables();
		applyAnnotationOnProcesses();

		inferVariableTypes();

		checkAllTyped();
	}

	/**
	 * Checks that all the information is typed
	 *
	 * @throws PGoTransException
	 *             as appropriate when not all information is typed
	 */
	private void checkAllTyped() throws PGoTransException {
		Map<PGoTypeVariable, PGoType> mapping = data.solver.getMapping();
		checkVariablesTyped(mapping);
		checkFunctionsTyped(mapping);
		// checkTLAExpressionsTyped(mapping);
	}

	private void checkFunctionsTyped(Map<PGoTypeVariable, PGoType> mapping) throws PGoTransException {
		for (PGoFunction f : this.data.funcs.values()) {
			f.setReturnType(f.getReturnType().substitute(mapping).realize());
			if (f.getReturnType().containsVariables()) {
				throw new PGoTransException("Unable to determine return type of function \"" + f.getName() + "()\"",
						f.getLine());
			}
			for (PGoVariable v : f.getParams()) {
				PGoType varType = PGoTypeUtil.substituteRealizeAndGetVariableType(v, mapping);
				if (varType.containsVariables()) {
					throw new PGoTransException("Unable to determine type of parameter \"" + v.getName()
							+ "\" in function \"" + f.getName() + "()\"", v.getLine());
				}
			}
			for (PGoVariable v : f.getVariables()) {
				PGoType varType = PGoTypeUtil.substituteRealizeAndGetVariableType(v, mapping);
				if (varType.containsVariables()) {
					throw new PGoTransException("Unable to determine type of local variable \"" + v.getName()
							+ "\" in function \"" + f.getName() + "()\"", v.getLine());
				}
			}
		}

	}

	private void checkVariablesTyped(Map<PGoTypeVariable, PGoType> mapping) throws PGoTransException {
		for (PGoVariable v : this.data.globals.values()) {
			PGoType varType = PGoTypeUtil.substituteRealizeAndGetVariableType(v, mapping);
			if (varType.containsVariables()) {
				throw new PGoTransException("Unable to determine type of global variable \"" + v.getName() + "\"",
						v.getLine());
			}
		}
		for (PGoVariable v : this.data.unresolvedVars.values()) {
			PGoType varType = PGoTypeUtil.substituteRealizeAndGetVariableType(v, mapping);
			if (varType.containsVariables()) {
				throw new PGoTransException("Unable to determine type of variable \"" + v.getName() + "\"",
						v.getLine());
			}
		}
	}

	// private void checkTLAExpressionsTyped(Map<PGoTypeVariable,PGoType> mapping) throws PGoTransException {
	// 	for (Map.Entry<TLAExprPgo, PGoTLAExpression> entry : data.tlaToAST.entrySet()) {
	// 		PGoTLAExpression v = entry.getValue();
	// 		if (v.getType() == null) {
	// 			throw new PGoTransException("Unable to determine type of expression", v.getLine());
	// 		}
	// 		v.setType(v.getType().substitute(mapping).realize());
	// 		if (v.getType().containsVariables()) {
	// 			throw new PGoTransException("Unable to determine type of expression", v.getLine());
	// 		}
	// 	}
	// }

	// Add typing information to the process functions' ID
	private void applyAnnotationOnProcesses() throws PGoTransException {
		for (AnnotatedProcess prcs : this.data.annots.getAnnotatedProcesses()) {
			PGoFunction fun = this.data.findPGoFunction(prcs.getName());
			if (fun == null) {
				throw new PGoTransException(
						"Reference to process function \"" + prcs.getName()
								+ "\" in annotation but no matching function or \"PGo " + prcs.getName() + "\" found.",
						prcs.getLine());
			}
			prcs.applyAnnotationOnFunction(fun);
		}
	}

	// Add annotation information of return variables
	private void applyAnnotationOnReturnVariables() throws PGoTransException {
		for (AnnotatedReturnVariable r : this.data.annots.getReturnVariables()) {
			r.applyAnnotation(this.data.globals, this.data.funcs.values());
		}
	}

	// Add annotation information of functions
	private void applyAnnotationOnFunctions() throws PGoTransException {
		for (AnnotatedFunction f : this.data.annots.getAnnotatedFunctions()) {
			PGoFunction fun = this.data.findPGoFunction(f.getName());
			if (fun == null) {
				throw new PGoTransException(
						"Reference to function \"" + f.getName() + "\" in annotation but no matching function \""
								+ f.getName() + "\" found.",
						f.getLine());
			}

			f.applyAnnotationOnFunction(fun, this.data.annots.getReturnVariables());
		}
	}

	// Add annotation information of variables
	private void applyAnnotationOnVariables() {
		for (AnnotatedVariable v : this.data.annots.getAnnotatedVariables()) {
			PGoVariable var = this.data.findPGoVariable(v.getName());
			if (var == null) {
				var = PGoVariable.convert(v.getName(), data.typeGenerator.get());
				var.setLine(v.getLine());
				if (v instanceof VarAnnotatedVariable) {
					// normal variable that we haven't encountered
					// this means the variable is probably defined in a "with"
					// clause or something, so don't store it as a global. Keep
					// it at the side for now.
					this.data.unresolvedVars.put(v.getName(), var);
				} else {
					this.data.globals.put(v.getName(), var);
				}
			}
			v.applyAnnotationOnVariable(var);

		}
	}

	// Parse annotated TLA definitions and add parsed version to data
	private void addAnnotatedDefinitions() throws PGoTransException {
		for (AnnotatedTLADefinition d : this.data.annots.getAnnotatedTLADefinitions()) {
			// if there are no parameters, compile to a variable
			if (d.getParams().isEmpty()) {
				PGoVariable var = PGoVariable.convert(d, new PGoTempData(data));
				this.data.globals.put(var.getName(), var);
				List<PGoTLAExpression> ptla = new TLAExprParser(d.getExpr(), d.getLine()).getResult();
				if (ptla.size() != 1) {
					throw new PGoTransExpectedSingleExpressionException(d.getLine());
				}
				this.data.putPGoTLA(d.getExpr(), ptla.get(0));
			} else {
				PGoTLADefinition tla = new PGoTLADefinition(d.getName(), d.getParams(), d.getExpr(), d.getType(),
						d.getLine());
				this.data.defns.put(d.getName(), tla);
			}
		}
	}

	// Infer types of variables based on the TLA expressions used in assignment.
	private void inferVariableTypes() throws PGoTransException {
		new PcalASTUtil.Walker<Void>() {
			@Override
			protected void init() {}

			@Override
			public Void getResult(AST body) throws PGoTransException {
				init();
				return super.getResult(body);
			}

			@Override
			protected void visit(AST.While w) throws PGoTransException {
				PGoTLAExpression cond = data.findPGoTLA(w.test);
				data.solver.accept(new PGoTypeConstraint(
						new TLAExprToType(cond, new PGoTempData(data)).getType(),
						PGoTypeBool.getInstance(),
						cond.getLine()));
				super.visit(w);
			}

			@Override
			protected void visit(AST.If ifast) throws PGoTransException {
				PGoTLAExpression cond = data.findPGoTLA(ifast.test);
				data.solver.accept(new PGoTypeConstraint(
						new TLAExprToType(cond, new PGoTempData(data)).getType(),
						PGoTypeBool.getInstance(),
						cond.getLine()));
				super.visit(ifast);
			}

			@Override
			protected void visit(AST.With with) throws PGoTransException {
				PGoTransIntermediateData oldData = data;
				data = new PGoTempData(data);
				AST cur = with;
				while (cur instanceof AST.With) {
					with = (AST.With) cur;
					String varName = with.var;
					PGoTLAExpression varExpr = data.findPGoTLA(with.exp);
					if (with.isEq) {
						// x = e
						((PGoTempData) data).getLocals().put(
								varName,
								PGoVariable.convert(varName, new TLAExprToType(varExpr, (PGoTempData) data).getType()));
					} else {
						// x \in S
						PGoType t = new TLAExprToType(varExpr, (PGoTempData) data).getType();
						PGoType fresh = data.typeGenerator.get();
						data.solver.accept(new PGoTypeConstraint(t, new PGoTypeSet(fresh), with.line));
						((PGoTempData) data).getLocals().put( varName, PGoVariable.convert(varName, fresh));
					}
					// if there are multiple statements, this is no longer a nested with
					if (with.Do.size() > 1) {
						break;
					}
					cur = (AST) with.Do.get(0);
				}
				walk(with.Do);
				data = oldData;
			}

			@Override
			protected void visit(AST.When when) throws PGoTransException {
				PGoTLAExpression cond = data.findPGoTLA(when.exp);
				data.solver.accept(new PGoTypeConstraint(
						new TLAExprToType(cond, new PGoTempData(data)).getType(),
						PGoTypeBool.getInstance(),
						cond.getLine()));
			}

			@Override
			protected void visit(AST.PrintS ps) throws PGoTransException {
				PGoTLAExpression exp = data.findPGoTLA(ps.exp);
				PGoType t = new TLAExprToType(exp, new PGoTempData(data)).getType();
				if (exp instanceof PGoTLAArray) {
					List<PGoType> elemTypes = ((PGoTLAArray) exp).getContents()
							.stream()
							.map(e -> data.typeGenerator.get())
							.collect(Collectors.toList());
					data.solver.accept(new PGoTypeConstraint(t, new PGoTypeTuple(elemTypes), exp.getLine()));
				}
			}

			@Override
			protected void visit(AST.LabelIf lif) throws PGoTransException {
				PGoTLAExpression cond = data.findPGoTLA(lif.test);
				data.solver.accept(new PGoTypeConstraint(
						new TLAExprToType(cond, new PGoTempData(data)).getType(),
						PGoTypeBool.getInstance(),
						cond.getLine()));
				super.visit(lif);
			}

			@Override
			protected void visit(AST.Call c) throws PGoTransException {
				PGoFunction func = data.findPGoFunction(c.to);
				if (func == null) {
					throw new PGoTransException("Unknown procedure " + c.to, c.line);
				}
				List<PGoType> callParams = new Vector<>();
				for (TLAExpr e : (Vector<TLAExpr>) c.args) {
					callParams.add(new TLAExprToType(data.findPGoTLA(e), new PGoTempData(data)).getType());
				}
				List<PGoType> funcParams = func.getParams().stream().map(PGoVariable::getType).collect(Collectors.toList());
				data.solver.accept(new PGoTypeConstraint(
						new PGoTypeFunction(callParams, func.getReturnType()),
						new PGoTypeFunction(funcParams, func.getReturnType()),
						c.line));
			}

			@Override
			protected void visit(AST.CallReturn cr) throws PGoTransException {
				PGoFunction func = data.findPGoFunction(cr.to);
				if (func == null) {
					throw new PGoTransException("Unknown procedure " + cr.to, cr.line);
				}
				List<PGoType> callParams = new Vector<>();
				for (TLAExpr e : (Vector<TLAExpr>) cr.args) {
					callParams.add(new TLAExprToType(data.findPGoTLA(e), new PGoTempData(data)).getType());
				}
				List<PGoType> funcParams = func.getParams().stream().map(PGoVariable::getType).collect(Collectors.toList());
				data.solver.accept(new PGoTypeConstraint(
						new PGoTypeFunction(callParams, func.getReturnType()),
						new PGoTypeFunction(funcParams, func.getReturnType()),
						cr.line));
			}

			@Override
			protected void visit(Process p) throws PGoTransException {
				Map<PGoTypeVariable, PGoType> mapping = PGoTypeUtil.unifyAndGetMapping(data.solver);
				PGoTLAExpression tla = data.findPGoTLA(p.id);
				PGoFunction fun = data.findPGoFunction(p.name);
				PGoVariable pId = fun.getParam(PGoVariable.PROCESS_VAR_ARG);

				PGoType type = new TLAExprToType(tla, new PGoTempData(data)).getType();
				if (p.isEq) {
					data.solver.accept(new PGoTypeConstraint(
							PGoTypeUtil.substituteAndGetVariableType(pId, mapping),
							type,
							tla.getLine()));
				} else {
					data.solver.accept(new PGoTypeConstraint(
							new PGoTypeSet(PGoTypeUtil.substituteAndGetVariableType(pId, mapping)),
							type,
							tla.getLine()));
				}
				// add "self" to data
				PGoTempData temp = new PGoTempData(data);
				PGoTransIntermediateData oldData = data;
				data = temp;
				temp.globals.put(PGoVariable.PROCESS_VAR_ARG, pId);
				// walk process ast
				super.visit(p);
				data = oldData;
			}

			@Override
			protected void visit(PVarDecl a) throws PGoTransException {
				visit(a.toVarDecl());
			}

			@Override
			protected void visit(VarDecl a) throws PGoTransException {
				Map<PGoTypeVariable, PGoType> mapping = PGoTypeUtil.unifyAndGetMapping(data.solver);
				PGoTLAExpression tla = data.findPGoTLA(a.val);
				PGoType varType = PGoTypeUtil.substituteAndGetVariableType(data.findPGoVariable(a.var), mapping);
				PGoType type = new TLAExprToType(tla, new PGoTempData(data)).getType();
				if (a.isEq) {
					data.solver.accept(new PGoTypeConstraint(varType, type, tla.getLine()));
				} else {
					data.solver.accept(new PGoTypeConstraint(type, new PGoTypeSet(varType), tla.getLine()));
				}
			}

			@Override
			protected void visit(SingleAssign sa) throws PGoTransException {
				Map<PGoTypeVariable, PGoType> mapping = PGoTypeUtil.unifyAndGetMapping(data.solver);
				PGoTLAExpression tla = data.findPGoTLA(sa.rhs);
				PGoVariable var = data.findPGoVariable(sa.lhs.var);
				PGoType varType = PGoTypeUtil.substituteAndGetVariableType(var, mapping);
				PGoType type = new TLAExprToType(tla, new PGoTempData(data)).getType();
				if (sa.lhs.sub.tokens.isEmpty()) {
					// no sub
					data.solver.accept(new PGoTypeConstraint(varType, type, tla.getLine()));
					return;
				}

				// the sub is [expr, expr...] (map/array access) or
				// .<name> for a record field

				PGoTLAExpression ptla = data.findPGoTLA(sa.lhs.sub);
				// TODO handle record fields
				PGoTLAFunctionCall fc = (PGoTLAFunctionCall) ptla;

				// if varType is an unrealized tuple representing a slice, it can be treated as a slice
				if (varType instanceof PGoTypeUnrealizedTuple &&
						((PGoTypeUnrealizedTuple) varType).getRealType() == PGoTypeUnrealizedTuple.RealType.Slice) {
					var.setType(varType.realize());
					varType = var.getType();
				}
				if (varType instanceof PGoTypeSlice) {
					data.solver.accept(new PGoTypeConstraint(varType, new PGoTypeSlice(type), tla.getLine()));
					return;
				}

				if (varType instanceof PGoTypeTuple || varType instanceof PGoTypeUnrealizedTuple) {
					if (!(fc.getParams().get(0) instanceof PGoTLANumber)) {
						return;
					}
					int index = Integer.parseInt(((PGoTLANumber) fc.getParams().get(0)).getVal());
					if (index < 0) {
						throw new PGoTransException("Trying to access a negative index of a tuple", tla.getLine());
					}
					if (varType instanceof PGoTypeTuple) {
						List<PGoType> elementTypes =  ((PGoTypeTuple) varType).getElementTypes();
						if (elementTypes.size() <= index) {
							throw new PGoTransException("Trying to access index " + index + " of " + varType.toTypeName(), tla.getLine());
						}
						data.solver.accept(new PGoTypeConstraint(varType, elementTypes.get(index), tla.getLine()));
					} else {
						Map<Integer, PGoType> elementTypes = ((PGoTypeUnrealizedTuple) varType).getElementTypes();
						if (elementTypes.containsKey(index)) {
							data.solver.accept(new PGoTypeConstraint(elementTypes.get(index), varType, tla.getLine()));
						}
					}
					return;
				}

				// if there are multiple indices, or the index is not an integer, then this is also a map
				PGoType indexType = new TLAExprToType(fc.getParams().get(0), new PGoTempData(data)).getType();
				if (varType instanceof PGoTypeMap || fc.getParams().size() > 1 ||
						!(indexType instanceof PGoTypeVariable) && !indexType.equals(PGoTypeNatural.getInstance()) &&
								!indexType.equals(PGoTypeInt.getInstance()) &&
								!indexType.equals(new PGoTypeUnrealizedNumber(PGoTypeDecimal.getInstance())) &&
								!indexType.equals(new PGoTypeUnrealizedNumber(PGoTypeInt.getInstance()))) {
					// we should also try to infer the key type
					Map<Integer, PGoType> key = new HashMap<>();
					List<PGoTLAExpression> params = fc.getParams();
					for (int i = 0; i < params.size(); i++) {
						PGoTLAExpression param = params.get(i);
						key.put(i, new TLAExprToType(param, new PGoTempData(data)).getType());
					}
					PGoType kTypeInferred;
					if (key.size() == 1) {
						kTypeInferred = key.get(0);
					} else {
						kTypeInferred = new PGoTypeUnrealizedTuple(key);
					}
					data.solver.accept(new PGoTypeConstraint(varType, new PGoTypeMap(kTypeInferred, type), tla.getLine()));
				}
			}

		}.getResult(data.ast);
		data.solver.unify();
		data.solver.simplify();
	}
}
