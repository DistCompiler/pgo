package pgo.trans.intermediate;

import pgo.model.golang.GoDeclaration;
import pgo.model.golang.GoModule;

import java.util.ArrayList;
import java.util.List;

public class CodeNormalisingPass {
	
	private CodeNormalisingPass() {}
	
	public static GoModule perform(GoModule module) {
		List<GoDeclaration> decls = new ArrayList<>();
		for(GoDeclaration decl : module.getDeclarations()) {
			decls.add(decl.accept(new GoDeclarationNormalisingVisitor()));
		}
		return new GoModule(module.getName(), module.getPackage(), module.getImports(), decls);
	}

}
