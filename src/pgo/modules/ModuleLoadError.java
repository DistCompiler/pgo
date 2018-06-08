package pgo.modules;

public class ModuleLoadError extends Exception {
	
	String moduleName;
	
	public ModuleLoadError(String name, Exception cause) {
		super("Error loading module \"" + name + "\"", cause);
	}
	
	public String getModuleName() {
		return moduleName;
	}
}
