package pgo.modules;

import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collections;
import java.util.List;

import pgo.lexer.PGoTLALexerException;
import pgo.lexer.TLALexer;
import pgo.lexer.TLAToken;
import pgo.model.tla.PGoTLAModule;
import pgo.parser.ParseContext;
import pgo.parser.TLAParseException;
import pgo.parser.TLAParser;

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
	
	public PGoTLAModule loadModule(String name) throws ModuleNotFoundError, IOException, PGoTLALexerException, TLAParseException, NoModulesFoundInFileError {
		Path modulePath = findModule(name);
		FileChannel fileChannel = new RandomAccessFile(modulePath.toFile(), "r").getChannel();
		MappedByteBuffer buffer = fileChannel.map(FileChannel.MapMode.READ_ONLY, 0, fileChannel.size());
		// assume UTF-8, though technically TLA+ is ASCII only according to the book
		ParseContext ctx = new ParseContext(modulePath, StandardCharsets.UTF_8.decode(buffer));
		List<PGoTLAModule> modules = TLAParser.readModules(ctx);
		if(modules.size() == 0) {
			throw new NoModulesFoundInFileError();
		}
		return modules.get(0);
	}
}
