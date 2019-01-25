package pgo.trans.passes.scope;

import pgo.errors.IssueContext;
import pgo.scope.UID;
import pgo.trans.intermediate.QualifiedName;
import pgo.trans.passes.scope.TLAScopeBuilder;

import java.util.Map;

public class TLAInstanceScopeBuilder extends TLAScopeBuilder {

	TLAScopeBuilder parent;
	String prefix;
	boolean isLocal;
	
	public TLAInstanceScopeBuilder(IssueContext ctx, Map<String, UID> declarations, Map<QualifiedName, UID> definitions,
			Map<UID, UID> references, TLAScopeBuilder parent, String prefix, boolean isLocal) {
		super(ctx, declarations, definitions, references);
		this.parent = parent;
		this.prefix = prefix;
		this.isLocal = isLocal;
	}
	
	@Override
	public void defineGlobal(QualifiedName name, UID id) {
		super.defineGlobal(name, id);
		QualifiedName withPrefix = prefix != null ? name.withPrefix(prefix) : name;
		if(isLocal) {
			parent.defineLocal(withPrefix, id);
		}else {
			parent.defineGlobal(withPrefix, id);
		}
	}

}
