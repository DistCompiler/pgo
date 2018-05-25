package pgo;

import java.util.ArrayList;
import java.util.List;

import pgo.model.golang.Declaration;
import pgo.model.golang.Module;

public class CodeNormalisingPass {
	
	private CodeNormalisingPass() {}
	
	public static Module perform(Module module) {
		List<Declaration> decls = new ArrayList<>();
		for(Declaration decl : module.getDeclarations()) {
			//decls.add(decl.accept(new GoDeclarationNormalisingVisitor()));
			decls.add(decl); // TODO
		}
		return new Module(module.getName(), module.getPackage(), module.getImports(), decls);
	}

}
