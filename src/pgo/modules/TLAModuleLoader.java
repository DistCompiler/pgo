package pgo.modules;

import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.tla.TLAModule;
import pgo.parser.LexicalContext;
import pgo.parser.ModularPlusCalParser;
import pgo.parser.ParseFailureException;
import pgo.parser.TLAParser;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.util.List;
import java.util.Optional;

public class TLAModuleLoader {
	private final List<Path> lookupPaths;
	
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

	private LexicalContext getContext(String name) throws ModuleNotFoundError, IOException {
		Path modulePath = findModule(name);
		FileChannel fileChannel = new RandomAccessFile(modulePath.toFile(), "r").getChannel();
		MappedByteBuffer buffer = fileChannel.map(FileChannel.MapMode.READ_ONLY, 0, fileChannel.size());
		// assume UTF-8, though technically TLA+ is ASCII only according to the book
		return new LexicalContext(modulePath, StandardCharsets.UTF_8.decode(buffer));
	}
	
	public TLAModule loadModule(String name)
			throws ModuleNotFoundError, IOException, ParseFailureException, NoModulesFoundInFileError {
		List<TLAModule> modules = TLAParser.readModules(getContext(name));
		if(modules.size() == 0) {
			throw new NoModulesFoundInFileError();
		}
		return modules.get(0);
	}

	public Optional<ModularPlusCalBlock> loadMPCal(String name) throws ModuleNotFoundError, IOException {
		try {
			return Optional.of(ModularPlusCalParser.readBlock(getContext(name)));
		} catch (ParseFailureException e) {
			return Optional.empty();
		}
	}
}
