package pgo.trans.intermediate;

import pgo.model.tla.TLAModule;
import pgo.scope.UID;

import java.util.List;
import java.util.Map;

public class TLAModuleRecord {
	
	TLAModule ast;
	List<String> submodules;
	Map<String, UID> declarations;
	Map<QualifiedName, UID> definitions;
	
	

}
