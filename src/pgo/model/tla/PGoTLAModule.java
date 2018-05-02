package pgo.model.tla;

import java.util.List;
import java.util.Map;

/**
 * 
 * TLA AST Node:
 * 
 * ---- ModuleName ----
 * EXTENDS ModuleA, ModuleB
 * ...
 * ====
 *
 */
public class PGoTLAModule extends PGoTLANode {
	
	String name;
	List<String> exts;
	List<String> variables;
	List<PGoTLAOpDecl> constants;
	Map<String, PGoTLAOperator> operators;
	List<PGoTLAModule> submodules;
	List<PGoTLAExpression> assumptions;
	List<PGoTLAExpression> theorems;

	public PGoTLAModule(String name, List<String> exts, List<String> variables, List<PGoTLAOpDecl> constants,
			Map<String, PGoTLAOperator> operators, List<PGoTLAModule> submodules, List<PGoTLAExpression> assumptions,
			List<PGoTLAExpression> theorems) {
		this.name = name;
		this.exts = exts;
		this.variables = variables;
		this.constants = constants;
		this.operators = operators;
		this.submodules = submodules;
		this.assumptions = assumptions;
		this.theorems = theorems;
	}
	
	public String getName() {
		return name;
	}
	
	public List<String> getExtends(){
		return exts;
	}
	
	public Map<String, PGoTLAOperator> getOperators(){
		return operators;
	}

	@Override
	public String toString() {
		return "PGoTLAModule [name=" + name + ", exts=" + exts + ", variables=" + variables + ", constants=" + constants
				+ ", operators=" + operators + ", submodules=" + submodules + ", assumptions=" + assumptions
				+ ", theorems=" + theorems + "]";
	}
	
}
