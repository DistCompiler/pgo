package pgo.modules;

import java.nio.file.Path;
import java.util.List;
import java.util.stream.Collectors;

public class ModuleNotFoundError extends Exception {
	
	String moduleName;
	List<Path> pathsChecked;
	
	public ModuleNotFoundError(String moduleName, List<Path> pathsChecked) {
		super(
				"GoModule not found: \"" + moduleName + "\", looked in " +
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
