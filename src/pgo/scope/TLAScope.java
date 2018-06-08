package pgo.scope;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import pgo.model.tla.PGoTLAGeneralIdentifierPart;
import pgo.model.tla.PGoTLAOperator;

public class TLAScope {
	
	public abstract class EntryVisitor<T>{
		public abstract T visit(OperatorEntry operatorEntry);
		public abstract T visit(NamespaceEntry namespaceEntry);
	}
	
	public abstract class Entry{
		public abstract <T> T accept(EntryVisitor<T> visitor);
	}
	
	public class OperatorEntry extends Entry{
		private PGoTLAOperator operator;

		public OperatorEntry(PGoTLAOperator operator) {
			this.operator = operator;
		}
		
		@Override
		public <T> T accept(EntryVisitor<T> visitor) {
			return visitor.visit(this);
		}
		
		public PGoTLAOperator getOperator() {
			return operator;
		}
	}
	
	public class NamespaceEntry extends Entry{
		private Map<String, Entry> scope;

		public NamespaceEntry(Map<String, Entry> scope) {
			this.scope = scope;
		}
		
		@Override
		public <T> T accept(EntryVisitor<T> visitor) {
			return visitor.visit(this);
		}
		
		public Map<String, Entry> getScope() {
			return scope;
		}
	}
	
	public class OperatorCheck extends EntryVisitor<PGoTLAOperator>{
		@Override
		public PGoTLAOperator visit(NamespaceEntry e) {
			// TODO Auto-generated method stub
			return null;
		}
		@Override
		public PGoTLAOperator visit(OperatorEntry e) {
			return e.getOperator();
		}
	}
	
	public class NamespaceCheck extends EntryVisitor<Map<String, Entry>>{
		@Override
		public Map<String, Entry> visit(NamespaceEntry e){
			return e.getScope();
		}

		@Override
		public Map<String, Entry> visit(OperatorEntry operatorEntry) {
			// TODO Auto-generated method stub
			return null;
		}
	}

	Map<String, Entry> scope;
	
	public TLAScope() {
		this.scope = new HashMap<String, Entry>();
	}
	
	Entry findWithPrefix(String name, List<PGoTLAGeneralIdentifierPart> prefix) {
		Map<String, Entry> currentScope = scope;
		
		for(PGoTLAGeneralIdentifierPart part : prefix) {
			currentScope = currentScope.get(part.getId()).accept(new NamespaceCheck());
		}
		
		return currentScope.get(name);
	}
	
	public PGoTLAOperator getOperator(String name, List<PGoTLAGeneralIdentifierPart> prefix) {
		return findWithPrefix(name, prefix).accept(new OperatorCheck());
	}
	
	public void putOperator(String name, PGoTLAOperator op) {
		scope.put(name, new OperatorEntry(op));
	}
	
	public void putNestedScope(String name, TLAScope scope) {
		this.scope.put(name, new NamespaceEntry(scope.scope));
	}
}
