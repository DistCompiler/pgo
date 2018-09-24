package pgo.trans.intermediate;

import pgo.errors.Context;
import pgo.errors.IssueContext;
import pgo.scope.ChainMap;
import pgo.scope.UID;

import java.util.HashMap;
import java.util.Map;

public class TLAScopeBuilder {
	Map<String, UID> declarations;
	Map<QualifiedName, UID> definitions;
	
	Map<UID, UID> references;
	
	IssueContext ctx;
	
	public TLAScopeBuilder(IssueContext ctx, Map<UID, UID> references) {
		this.ctx = ctx;
		this.declarations = new HashMap<>();
		this.definitions = TLABuiltins.getInitialDefinitions();
		this.references = references;
	}
	
	public TLAScopeBuilder(IssueContext ctx, Map<String, UID> declarations, Map<QualifiedName, UID> definitions, Map<UID, UID> references) {
		super();
		this.ctx = ctx;
		this.declarations = declarations;
		this.definitions = definitions;
		this.references = references;
	}
	
	public TLAScopeBuilder makeNestedScope() {
		return new TLAScopeBuilder(ctx, declarations, new ChainMap<>(definitions), references);
	}
	
	public TLAScopeBuilder makeNestedScope(Context context) {
		return new TLAScopeBuilder(ctx.withContext(context), declarations, new ChainMap<>(definitions), references);
	}
	
	public IssueContext getIssueContext() {
		return ctx;
	}
	
	public Map<String, UID> getDeclarations(){
		return declarations;
	}
	
	public Map<UID, UID> getReferences(){
		return references;
	}
	
	public boolean declare(String name, UID id) {
		QualifiedName qname = new QualifiedName(name);
		if (declarations.containsKey(name)) {
			ctx.error(new ScopeConflictIssue(name, declarations.get(name), id));
			return false;
		}else if(definitions.containsKey(qname)) {
			ctx.error(new ScopeConflictIssue(name, definitions.get(qname), id));
			return false;
		}else {
			declarations.put(name, id);
			return true;
		}
	}
	
	public void defineLocal(QualifiedName name, UID id) {
		if(name.getPrefix().isEmpty() && declarations.containsKey(name.getBase())) {
			ctx.error(new ScopeConflictIssue(name, declarations.get(name.getBase()), id));
		}else if(definitions.containsKey(name)) {
			ctx.error(new ScopeConflictIssue(name, definitions.get(name), id));
		}else {
			definitions.put(name,  id);
		}
	}
	
	public void defineLocal(String name, UID id) {
		defineLocal(new QualifiedName(name), id);
	}
	
	public void defineGlobal(QualifiedName name, UID id) {
		defineLocal(name, id);
	}
	
	public void defineGlobal(String name, UID id) {
		defineGlobal(new QualifiedName(name), id);
	}
	
	public void reference(QualifiedName to, UID from) {
		if(to.getPrefix().isEmpty() && declarations.containsKey(to.getBase())) {
			references.put(from, declarations.get(to.getBase()));
		}else if(definitions.containsKey(to)) {
			references.put(from, definitions.get(to));
		}else{
			ctx.error(new DanglingReferenceIssue(from));
		}
	}

	public void reference(String to, UID from) {
		reference(new QualifiedName(to), from);
	}

	public Map<QualifiedName, UID> getDefinitions() {
		return definitions;
	}
	
}
