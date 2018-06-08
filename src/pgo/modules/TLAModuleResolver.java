package pgo.modules;

import java.util.Map;

import pgo.model.tla.PGoTLAModule;
import pgo.model.tla.PGoTLAOperator;
import pgo.scope.TLAScope;

public class TLAModuleResolver {
	
	TLAModuleLoader moduleLoader;
	
	public TLAModuleResolver(TLAModuleLoader moduleLoader) {
		this.moduleLoader = moduleLoader;
	}
	
	TLAScope resolveModuleScope(PGoTLAModule module) throws ModuleLoadError{
		TLAScope scope = new TLAScope();
		for(String ext : module.getExtends()) {
			PGoTLAModule nested = moduleLoader.loadModule(ext);
			TLAScope nestedScope = resolveModuleScope(nested);
			scope.putNestedScope(ext, nestedScope);
		}
		for(Map.Entry<String, PGoTLAOperator> op : module.getOperators().entrySet()) {
			scope.putOperator(op.getKey(), op.getValue());
		}
		return scope;
	}

}
