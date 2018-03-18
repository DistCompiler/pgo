package pgo.model.tla;

import java.util.Map;

/**
 * 
 * TLA AST Node:
 * 
 * INSTANCE ModuleName (WITH a <- <expr>, b <- <expr>)?
 *
 */
public class PGoTLAInstance {
	
	String referenceName;
	String moduleName;
	Map<PGoTLAOpDecl, PGoTLAExpression> remappings;
	
	public PGoTLAInstance(String referenceName, String moduleName, Map<PGoTLAOpDecl, PGoTLAExpression> remappings) {
		this.referenceName = referenceName;
		this.moduleName = moduleName;
		this.remappings = remappings;
	}
	
	public void setReferenceName(String referenceName) {
		this.referenceName = referenceName;
	}
	
	public String getReferenceName() {
		return referenceName;
	}
	
	public String getName() {
		return moduleName;
	}
	
	public Map<PGoTLAOpDecl, PGoTLAExpression> getRemappings(){
		return remappings;
	}
}
