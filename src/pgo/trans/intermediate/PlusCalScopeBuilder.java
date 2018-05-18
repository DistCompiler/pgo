package pgo.trans.intermediate;

import java.util.Map;

import pgo.errors.IssueContext;
import pgo.scope.UID;

public class PlusCalScopeBuilder {
	
	private IssueContext ctx;
	private Map<String, UID> tlaVariables;
	private Map<QualifiedName, UID> tlaDefinitions;
	private Map<String, UID> variables;
	private Map<String, UID> labels;
	private Map<UID, UID> references;
	
	public PlusCalScopeBuilder(IssueContext ctx, Map<String, UID> variables, Map<String, UID> labels,
			Map<UID, UID> references) {
		super();
		this.ctx = ctx;
		this.variables = variables;
		this.labels = labels;
		this.references = references;
	}
	
	public void declareLabel(String name, UID uid) {
		
	}

}
