package pgo.trans.intermediate;

import java.util.Map;
import java.util.Vector;

import pcal.AST;
import pcal.AST.PVarDecl;
import pcal.AST.Process;
import pcal.AST.SingleAssign;
import pcal.AST.VarDecl;
import pgo.PGoNetOptions;
import pgo.ProcessIntArg;
import pgo.ProcessStringArg;
import pgo.model.intermediate.*;
import pgo.model.intermediate.PGoCollectionType.PGoMap;
import pgo.model.intermediate.PGoCollectionType.PGoSet;
import pgo.model.intermediate.PGoCollectionType.PGoSlice;
import pgo.model.intermediate.PGoCollectionType.PGoTuple;
import pgo.model.intermediate.PGoPrimitiveType.PGoInt;
import pgo.model.intermediate.PGoPrimitiveType.PGoNatural;
import pgo.model.parser.AnnotatedFunction;
import pgo.model.parser.AnnotatedProcess;
import pgo.model.parser.AnnotatedReturnVariable;
import pgo.model.parser.AnnotatedTLADefinition;
import pgo.model.parser.AnnotatedVariable;
import pgo.model.parser.AnnotatedVariable.VarAnnotatedVariable;
import pgo.model.tla.PGoTLA;
import pgo.model.tla.PGoTLADefinition;
import pgo.model.tla.PGoTLAFunctionCall;
import pgo.model.tla.PGoTLANumber;
import pgo.model.tla.TLAExprToType;
import pgo.parser.PGoParseException;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;
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

	public PGoTransStageType(PGoTransStageTLAParse s1) throws PGoParseException, PGoTransException {
		this.data = s1.data;

		addAnnotatedDefinitions();
		applyAnnotationOnVariables();
		applyAnnotationOnFunctions();
		applyAnnotationOnReturnVariables();
		applyAnnotationOnProcesses();

		inferVariableTypes();

		checkAllTyped();

		// config sanitization
		if (data.netOpts.isEnabled()) {
			for (Map.Entry<String, PGoNetOptions.Channel> entry : data.netOpts.getChannels().entrySet()) {
				PGoNetOptions.Channel channel = entry.getValue();
				for (PGoNetOptions.Process p : channel.processes) {
					PGoType type = this.data.funcs.get(p.name).getParam("self").getType();
					if (type.equals(PGoPrimitiveType.INT) && p.arg instanceof ProcessStringArg) {
						throw new PGoParseException("Argument for process " + p.name + " expected to be string, found int");
					}
					if (type.equals(PGoPrimitiveType.STRING) && p.arg instanceof ProcessIntArg) {
						throw new PGoParseException("Argument for process " + p.name + " expected to be int, found string");
					}
				}
			}
		}
	}

	/**
	 * Checks that all the information is typed
	 * 
	 * @throws PGoTransException
	 *             as appropriate when not all information is typed
	 */
	private void checkAllTyped() throws PGoTransException {
		checkVariablesTyped();
		checkFunctionsTyped();
	}

	private void checkFunctionsTyped() throws PGoTransException {
		for (PGoFunction f : this.data.funcs.values()) {
			if (f.getReturnType().isUndetermined()) {
				throw new PGoTransException("Unable to determine return type of function \"" + f.getName() + "()\"",
						f.getLine());
			}
			for (PGoVariable v : f.getParams()) {
				if (v.getType().isUndetermined()) {
					throw new PGoTransException("Unable to determine type of parameter \"" + v.getName()
							+ "\" in function \"" + f.getName() + "()\"", v.getLine());
				}
			}
			for (PGoVariable v : f.getVariables()) {
				if (v.getType().isUndetermined()) {
					throw new PGoTransException("Unable to determine type of local variable \"" + v.getName()
							+ "\" in function \"" + f.getName() + "()\"", v.getLine());
				}
			}
		}

	}

	private void checkVariablesTyped() throws PGoTransException {
		for (PGoVariable v : this.data.globals.values()) {
			if (v.getType().isUndetermined()) {
				throw new PGoTransException("Unable to determine type of global variable \"" + v.getName() + "\"",
						v.getLine());
			}
		}
		for (PGoVariable v : this.data.unresolvedVars.values()) {
			if (v.getType().isUndetermined()) {
				throw new PGoTransException("Unable to determine type of variable \"" + v.getName() + "\"",
						v.getLine());
			}
		}
	}

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
				var = PGoVariable.convert(v.getName());
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
	private void addAnnotatedDefinitions() throws PGoTransException, PGoParseException {
		for (AnnotatedTLADefinition d : this.data.annots.getAnnotatedTLADefinitions()) {
			// if there are no parameters, compile to a variable
			if (d.getParams().isEmpty()) {
				PGoVariable var = PGoVariable.convert(d, new PGoTempData(data));
				this.data.globals.put(var.getName(), var);
				Vector<PGoTLA> ptla = new TLAExprParser(d.getExpr(), d.getLine()).getResult();
				assert (ptla.size() == 1);
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
		PcalASTUtil.Walker<Boolean> walker = new PcalASTUtil.Walker<Boolean>() {

			@Override
			protected void init() {
				// whether we were able to infer something new in this pass
				result = false;
			}

			@Override
			public Boolean getResult(AST body) throws PGoTransException {
				init();
				return super.getResult(body);
			}

			@Override
			protected void visit(Process p) throws PGoTransException {
				// infer the type of the process id
				PGoTLA tla = data.findPGoTLA(p.id);
				PGoFunction fun = data.findPGoFunction(p.name);
				PGoVariable pId = fun.getParam(PGoVariable.processIdArg().getName());

				PGoType type;
				if (p.isEq) {
					type = new TLAExprToType(tla, new PGoTempData(data), pId, false).getType();
				} else {
					type = new TLAExprToType(tla, new PGoTempData(data),
							PGoType.inferFromGoTypeName("set[" + pId.getType().toTypeName() + "]"), false).getType();
				}

				if (type != PGoType.UNDETERMINED) {
					if (!p.isEq) {
						// this is var \in set
						assert (type instanceof PGoSet);
						type = ((PGoSet) type).getElementType();
					}

					if (!type.equals(pId.getType())) {
						if (pId.getType() == PGoType.UNDETERMINED) {
							pId.setType(type);
							pId.setAsInferredType();
						} else {
							// already checked for type consistency in
							// TLAExprToType
							assert (TLAExprToType.compatibleType(type, pId.getType()) != null);
							// if the variable type didn't change, don't flag as
							// changed
							if (!pId.getType().equals(TLAExprToType.compatibleType(type, pId.getType()))) {
								pId.setType(TLAExprToType.compatibleType(type, pId.getType()));
								pId.setAsInferredType();
								result = true;
							}
						}
					}

				}

				// add "self" to data
				PGoTempData temp = new PGoTempData(data);
				PGoTransIntermediateData oldData = data;
				data = temp;
				temp.globals.put("self", pId);
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
				PGoTLA tla = data.findPGoTLA(a.val);
				PGoVariable var = data.findPGoVariable(a.var);
				PGoType type;
				if (a.isEq) {
					type = new TLAExprToType(tla, new PGoTempData(data), var, false).getType();
				} else {
					type = new TLAExprToType(tla, new PGoTempData(data),
							PGoType.inferFromGoTypeName("set[" + var.getType().toTypeName() + "]"), false).getType();
				}

				if (type == PGoType.UNDETERMINED) {
					return;
				}

				if (!a.isEq) {
					// this is var \in set
					assert (type instanceof PGoSet);
					type = ((PGoSet) type).getElementType();
				}

				if (type.equals(var.getType())) {
					return;
				}

				if (var.getType() == PGoType.UNDETERMINED) {
					var.setType(type);
					var.setAsInferredType();
				} else {
					// already checked for type consistency in TLAExprToType
					assert (TLAExprToType.compatibleType(type, var.getType()) != null);
					// if the variable type didn't change, don't flag as changed
					if (var.getType().equals(TLAExprToType.compatibleType(type, var.getType()))) {
						return;
					}
					var.setType(TLAExprToType.compatibleType(type, var.getType()));
					var.setAsInferredType();
				}

				result = true;
			}

			@Override
			protected void visit(SingleAssign sa) throws PGoTransException {
				PGoTLA tla = data.findPGoTLA(sa.rhs);
				PGoVariable var = data.findPGoVariable(sa.lhs.var);
				PGoType type;
				if (sa.lhs.sub.tokens.isEmpty()) {
					// no sub
					type = new TLAExprToType(tla, new PGoTempData(data), var, false).getType();

					if (type == PGoType.UNDETERMINED || var.getType().equals(type)) {
						return;
					}

					if (var.getType() == PGoType.UNDETERMINED) {
						var.setType(type);
						var.setAsInferredType();
					} else {
						assert (TLAExprToType.compatibleType(type, var.getType()) != null);
						// if the variable type didn't change, don't flag as
						// changed
						if (var.getType().equals(TLAExprToType.compatibleType(type, var.getType()))) {
							return;
						}
						var.setType(TLAExprToType.compatibleType(type, var.getType()));
						var.setAsInferredType();
					}
					result = true;
				} else {
					// the sub is [expr, expr...] (map/array access) or
					// .<name> for a record field

					PGoTLA ptla = data.findPGoTLA(sa.lhs.sub);
					// TODO handle record fields
					PGoTLAFunctionCall fc = (PGoTLAFunctionCall) ptla;

					// the element type of the variable
					PGoType givenType = PGoType.UNDETERMINED;
					if (var.getType() instanceof PGoMap || var.getType() instanceof PGoSlice) {
						givenType = ((PGoCollectionType) var.getType()).getElementType();
					}
					type = new TLAExprToType(ptla, new PGoTempData(data), givenType, false).getType();

					if (type == PGoType.UNDETERMINED) {
						return;
					}

					if (var.getType() == PGoType.UNDETERMINED) {
						// if there are multiple indices, or the index is not an
						// integer, then this is a map
						if (fc.getParams().size() > 1) {
							var.setType(new PGoMap("undetermined", "undetermined"));
							var.setAsInferredType();
						} else {
							PGoType indexType = new TLAExprToType(fc.getParams().get(0), new PGoTempData(data), false)
									.getType();
							if (indexType != PGoType.UNDETERMINED && !(indexType instanceof PGoNatural)
									&& !(indexType instanceof PGoInt)) {
								var.setType(new PGoMap(indexType.toTypeName(), "undetermined"));
								var.setAsInferredType();
							} else {
								return;
							}
						}
					}

					if (var.getType() instanceof PGoTuple) {
						if (fc.getParams().get(0) instanceof PGoTLANumber) {
							int index = Integer.parseInt(((PGoTLANumber) fc.getParams().get(0)).getVal());
							PGoType toSet = ((PGoTuple) var.getType()).getType(index);

							if (TLAExprToType.compatibleType(toSet, type).equals(toSet)) {
								return;
							}
							((PGoTuple) var.getType()).setType(index, type);
							var.setAsInferredType();
						} else {
							return;
						}
					} else if (var.getType() instanceof PGoSlice) {
						PGoType toSet = ((PGoSlice) var.getType()).getElementType();

						if (TLAExprToType.compatibleType(toSet, type).equals(toSet)) {
							return;
						}
						((PGoSlice) var.getType()).setElementType(type);
						var.setAsInferredType();
					} else if (var.getType() instanceof PGoMap) {
						PGoType eType = ((PGoMap) var.getType()).getElementType();
						PGoType kType = ((PGoMap) var.getType()).getKeyType();

						// we should also try to infer the key type
						Vector<PGoType> key = new Vector<>();
						for (PGoTLA param : fc.getParams()) {
							key.add(new TLAExprToType(param, new PGoTempData(data), false).getType());
						}

						PGoType kTypeInferred;
						if (key.size() == 1) {
							kTypeInferred = key.get(0);
						} else {
							kTypeInferred = new PGoTuple(key, false);
						}

						PGoType kNew = TLAExprToType.compatibleType(kTypeInferred, kType),
								eNew = TLAExprToType.compatibleType(type, eType);

						if ((type == PGoType.UNDETERMINED || eNew.equals(eType))
								&& (kTypeInferred == PGoType.UNDETERMINED || kNew.equals(kType))) {
							return;
						}

						((PGoMap) var.getType()).setElementType(eNew);
						((PGoMap) var.getType()).setKeyType(kNew);

						var.setAsInferredType();
					}
				}

				result = true;

			}

		};
		// walk the ast repeatedly, filling type information, until we cannot
		// infer any more types
		while (true) {
			if (!walker.getResult(data.ast)) {
				break;
			}
		}
	}
}
