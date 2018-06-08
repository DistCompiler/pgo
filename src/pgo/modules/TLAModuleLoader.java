package pgo.modules;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;
import java.util.stream.Collectors;

import pcal.TLAToken;
import pgo.lexer.PGoTLALexerException;
import pgo.lexer.TLALexer;
import pgo.model.tla.PGoTLAModule;
import pgo.parser.PGoTLAParseException;
import pgo.parser.TLAParser;

public class TLAModuleLoader {
	
	List<Path> lookupPaths;
	
	public TLAModuleLoader(List<Path> lookupPaths) {
		this.lookupPaths = lookupPaths;
	}
	
	Path findModule(String name) throws ModuleNotFoundError {
		for(Path p : lookupPaths) {
			Path result = p.resolve(name+".tla");
			if(result.toFile().exists()) {
				return result;
			}
		}
		throw new ModuleNotFoundError(name, lookupPaths);
	}
	
	public PGoTLAModule loadModule(String name) throws ModuleLoadError {
		try {
			Path modulePath = findModule(name);
			TLALexer lexer = new TLALexer(modulePath);
			List<TLAToken> tokens = lexer.readTokens();
			List<PGoTLAModule> modules = TLAParser.readModules(tokens.listIterator());
			if(modules.size() != 1) {
				throw new UnsupportedModuleConfigurationError(name, modules.stream().map(PGoTLAModule::getName).collect(Collectors.toList()));
			}
			return modules.get(0);
		}catch(UnsupportedModuleConfigurationError|IOException|PGoTLALexerException|
				PGoTLAParseException|ModuleNotFoundError ex) {
			// package any exceptions up into one overarching exception with cause left in
			throw new ModuleLoadError(name, ex);
		}
	}
}
