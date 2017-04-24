package pgo.trans.intermediate;

import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoVariable;
import pgo.model.parser.AnnotatedFunction;
import pgo.model.parser.AnnotatedProcess;
import pgo.model.parser.AnnotatedReturnVariable;
import pgo.model.parser.AnnotatedVariable;
import pgo.model.parser.AnnotatedVariable.VarAnnotatedVariable;
import pgo.parser.PGoAnnotationParser;
import pgo.parser.PGoParseException;
import pgo.parser.PcalParser.ParsedPcal;
import pgo.trans.PGoTransException;

/**
 * The second stage of the translation where we determine the types of all
 * variables and functions of the algorithm. This stage should end with all
 * variables' and functions' types being completely determined, otherwise a
 * PGoTransException will be thrown.
 *
 */
public class PGoTransStageType extends PGoTransStageBase {

	public PGoTransStageType(PGoTransStageOne s1, ParsedPcal pcal) throws PGoParseException, PGoTransException {
		super(s1);
		PGoAnnotationParser p = new PGoAnnotationParser(pcal.getPGoAnnotations());
		
		fixUpVariables(p);
		fixUpFunctions(p);
		fixUpReturnVariables(p);
		fixUpProcesses(p);

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
		for (PGoFunction f : this.intermediateData.funcs.values()) {
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
		for (PGoVariable v : this.intermediateData.globals.values()) {
			if (v.getType().isUndetermined()) {
				throw new PGoTransException("Unable to determine type of global variable \"" + v.getName() + "\"",
						v.getLine());
			}
		}
		for (PGoVariable v : this.intermediateData.tempVars.values()) {
			if (v.getType().isUndetermined()) {
				throw new PGoTransException("Unable to determine type of variable \"" + v.getName() + "\"",
						v.getLine());
			}
		}
	}

	private void fixUpProcesses(PGoAnnotationParser p) throws PGoTransException {
		for (AnnotatedProcess prcs : p.getAnnotatedProcesses()) {
			PGoFunction fun = this.intermediateData.findPGoFunction(prcs.getName());
			if (fun == null) {
				throw new PGoTransException(
						"Reference to process function \"" + prcs.getName()
								+ "\" in annotation but no matching function or \"PGo " + prcs.getName() + "\" found.",
						prcs.getLine());
			}
			prcs.fillFunction(fun);
		}
	}

	// Add annotation information of return variables
	private void fixUpReturnVariables(PGoAnnotationParser p) {
		for (AnnotatedReturnVariable r : p.getReturnVariables()) {
			r.fixUp(this.intermediateData.globals, this.intermediateData.funcs.values());
		}
	}

	// Add annotation information of functions
	private void fixUpFunctions(PGoAnnotationParser p) throws PGoTransException {
		for (AnnotatedFunction f : p.getAnnotatedFunctions()) {
			PGoFunction fun = this.intermediateData.findPGoFunction(f.getName());
			if (fun == null) {
				throw new PGoTransException(
							"Reference to function \"" + f.getName()
								+ "\" in annotation but no matching function \"" + f.getName() + " \"or \"PGo"
								+ f.getName() + "\" found.",
							f.getLine());
			}

			f.fillFunction(fun, p.getReturnVariables());
		}
	}

	// Add annotation information of variables
	private void fixUpVariables(PGoAnnotationParser p) {
		for (AnnotatedVariable v : p.getAnnotatedVariables()) {
			PGoVariable var = this.intermediateData.findPGoVariable(v.getName());
			if (var == null) {
				var = PGoVariable.convert(v.getName());
				var.setLine(v.getLine());
				if (v instanceof VarAnnotatedVariable) {
					// normal variable that we haven't encountered
					// this means the variable is probably defined in a "with"
					// clause or something, so don't store it as a global. Keep
					// it at the side for now.
					this.intermediateData.tempVars.put(v.getName(), var);
				} else {
					this.intermediateData.globals.put(v.getName(), var);
				}
			}
			v.fillVariable(var);

		}
	}


}
