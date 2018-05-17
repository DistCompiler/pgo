package pgo.trans.intermediate;

import java.util.List;
import java.util.Map;

import pgo.model.tla.PGoTLAModule;
import pgo.scope.UID;

public class TLAModuleRecord {
	
	PGoTLAModule ast;
	List<String> submodules;
	Map<String, UID> declarations;
	Map<QualifiedName, UID> definitions;
	
	

}
