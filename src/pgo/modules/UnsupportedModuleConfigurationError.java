package pgo.modules;

import java.util.List;

public class UnsupportedModuleConfigurationError extends Exception {
	
	List<String> actualModules;
	
	public UnsupportedModuleConfigurationError(String moduleName, List<String> actualModules) {
		super("Unsupported module configuration detected: " + String.join(", ", actualModules));
		this.actualModules = actualModules;
	}
	
	public List<String> getActualModules(){
		return actualModules;
	}
}
