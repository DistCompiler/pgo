package pgo.modules;

import pgo.model.tla.TLAModule;
import pgo.parser.LexicalContext;
import pgo.parser.ParseFailureException;
import pgo.parser.TLAParser;

import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.util.List;

public class TLAModuleLoader {
	
	List<Path> lookupPaths;
	
	public TLAModuleLoader(List<Path> lookupPaths) {
		this.lookupPaths = lookupPaths;
	}
	
	public Path findModule(String name) throws ModuleNotFoundError {
		for(Path p : lookupPaths) {
			Path result = p.resolve(name+".tla");
			if(result.toFile().exists()) {
				return result;
			}
		}
		throw new ModuleNotFoundError(name, lookupPaths);
	}
	
	public TLAModule loadModule(String name) throws ModuleNotFoundError, IOException, ParseFailureException, NoModulesFoundInFileError {
		Path modulePath = findModule(name);
		FileChannel fileChannel = new RandomAccessFile(modulePath.toFile(), "r").getChannel();
		MappedByteBuffer buffer = fileChannel.map(FileChannel.MapMode.READ_ONLY, 0, fileChannel.size());
		// assume UTF-8, though technically TLA+ is ASCII only according to the book
		LexicalContext ctx = new LexicalContext(modulePath, StandardCharsets.UTF_8.decode(buffer));
		List<TLAModule> modules = TLAParser.readModules(ctx);
		if(modules.size() == 0) {
			throw new NoModulesFoundInFileError();
		}
		return modules.get(0);
	}
}
