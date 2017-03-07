package pgo.trans.intermediate.model;

import pcal.AST;

/**
 * Intermediate representation of a single pluscal and golang variable.
 * 
 * PlusCal declares variables as `variable varname=val; varname2=val2;
 * varname3...` and may include PlusCal specific syntax initialization. GoLang
 * declares variables as `type var;` or `type var = val;` or more complex
 * initializations
 *
 */
public class PGoVariable {
	// the name of the variable
	private String name;

	// the pluscal ast code block corresponding to variable initialization
	private AST pcalInitBlock;
	// TODO types, initialization, etc

	public String getName() {
		return name;
	}

	public AST getPcalInitBlock() {
		return pcalInitBlock;
	}

	public void setName(String name) {
		this.name = name;
	}

	public void setPcalInitBlock(AST ast) {
		this.pcalInitBlock = ast;
	}
}
