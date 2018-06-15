package pgo.modules;

import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collections;
import java.util.List;

import pgo.lexer.PGoTLALexerException;
import pgo.lexer.TLALexer;
import pgo.lexer.TLAToken;
import pgo.model.tla.PGoTLAModule;
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
			List<String> lines = Collections.unmodifiableList(Files.readAllLines(modulePath, Charset.forName("utf-8")));
			TLALexer lexer = new TLALexer(modulePath, lines);
			List<TLAToken> tokens = lexer.readTokens();
			List<PGoTLAModule> modules = TLAParser.readModules(tokens.listIterator());
			if(modules.size() == 0) {
				throw new NoModulesFoundInFileError();
			}
			return modules.get(0);
	}
}
