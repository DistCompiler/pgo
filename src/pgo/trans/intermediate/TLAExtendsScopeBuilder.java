package pgo.trans.intermediate;

import java.util.Map;

import pgo.errors.IssueContext;
import pgo.scope.UID;

public class TLAExtendsScopeBuilder extends TLAScopeBuilder {

	private TLAScopeBuilder parent;
	private boolean isLocal;

	public TLAExtendsScopeBuilder(IssueContext ctx, Map<String, UID> declarations, Map<QualifiedName, UID> definitions,
			Map<UID, UID> references, TLAScopeBuilder parent, boolean isLocal) {
		super(ctx, declarations, definitions, references);
		this.parent = parent;
		this.isLocal = isLocal;
	}
	
	@Override
	public void defineGlobal(QualifiedName name, UID uid) {
		super.defineGlobal(name, uid);
		if(isLocal) {
			parent.defineLocal(name, uid);
		}else {
			parent.defineGlobal(name, uid);
		}
	}

}
