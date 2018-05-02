package pgo.modules;

import java.nio.file.Path;
import java.util.List;
import java.util.stream.Collectors;

public class ModuleNotFoundError extends Exception {
	/**
	 * Serial version ID
	 */
	private static final long serialVersionUID = -7527234825656001085L;
	
	String moduleName;
	List<Path> pathsChecked;
	
	public ModuleNotFoundError(String moduleName, List<Path> pathsChecked) {
		super(
				"Module not found: \"" + moduleName + "\", looked in " +
						pathsChecked.stream()
						.map(Path::toString)
						.collect(Collectors.joining(", ")));
		this.moduleName = moduleName;
		this.pathsChecked = pathsChecked;
	}
	
	public String getModuleName() {
		return moduleName;
	}
	
	public List<Path> getPathsChecked(){
		return pathsChecked;
	}
}
