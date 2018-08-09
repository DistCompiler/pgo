package pgo.trans.intermediate;

import java.util.List;
import java.util.Map;

import pgo.model.tla.TLAModule;
import pgo.scope.UID;

public class TLAModuleRecord {
	
	TLAModule ast;
	List<String> submodules;
	Map<String, UID> declarations;
	Map<QualifiedName, UID> definitions;
	
	

}
