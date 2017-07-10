package pgo.trans.intermediate;

import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoVariable;
import pgo.model.parser.AnnotatedFunction;
import pgo.model.parser.AnnotatedProcess;
import pgo.model.parser.AnnotatedReturnVariable;
import pgo.model.parser.AnnotatedTLADefinition;
import pgo.model.parser.AnnotatedVariable;
import pgo.model.parser.AnnotatedVariable.VarAnnotatedVariable;
import pgo.model.tla.PGoTLADefinition;
import pgo.parser.PGoParseException;
import pgo.trans.PGoTransException;

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

	public PGoTransStageType(PGoTransStageInitParse s1) throws PGoParseException, PGoTransException {
		this.data = s1.data;
		applyAnnotationOnVariables();
		applyAnnotationOnFunctions();
		applyAnnotationOnReturnVariables();
		applyAnnotationOnProcesses();
		addAnnotatedDefinitions();

		checkAllTyped();
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
						"Reference to function \"" + f.getName()
								+ "\" in annotation but no matching function \"" + f.getName() + " \"or \"PGo"
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
			PGoTLADefinition tla = new PGoTLADefinition(d.getName(), d.getParams(), d.getExpr(), d.getLine());
			this.data.defns.put(d.getName(), tla);
		}
	}
}
