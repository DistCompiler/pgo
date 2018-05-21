package pgo.trans;

import java.io.File;
import java.io.IOException;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.List;
import java.util.Vector;
import java.util.logging.Logger;

import org.apache.commons.io.FileUtils;

import pgo.PGoNetOptions;
import pgo.PGoOptions;
import pgo.errors.TopLevelIssueContext;
import pgo.model.pcal.Algorithm;
import pgo.model.tla.PGoTLAModule;
import pgo.modules.TLAModuleLoader;
import pgo.parser.PGoAnnotationParser;
import pgo.parser.PGoParseException;
import pgo.parser.PcalParser.ParsedPcal;
import pgo.trans.intermediate.AnnotationParsingPass;
import pgo.trans.intermediate.CheckOptionsPass;
import pgo.trans.intermediate.PGoScopingPass;
import pgo.trans.intermediate.PGoTransStageAtomicity;
import pgo.trans.intermediate.PGoTransStageGoGen;
import pgo.trans.intermediate.PGoTransStageInitParse;
import pgo.trans.intermediate.PGoTransStageTLAParse;
import pgo.trans.intermediate.PGoTransStageType;
import pgo.trans.intermediate.PlusCalConversionPass;
import pgo.trans.intermediate.PlusCalMacroExpansionPass;
import pgo.trans.intermediate.TLAParsingPass;

/**
 * Performs the translation of the PlusCal AST into a Golang AST
 * 
 */
public class PGoTranslator {

	private Logger logger;

	public PGoTranslator(ParsedPcal pcal, PGoNetOptions opts) throws PGoTransException, PGoParseException {

		logger = Logger.getGlobal();
		
		TopLevelIssueContext ctx = new TopLevelIssueContext();
		TLAModuleLoader loader = new TLAModuleLoader(Collections.emptyList()); // TODO: add paths
		
		logger.info("Parsing TLA+ module");
		PGoTLAModule tlaModule = TLAParsingPass.perform(ctx, Paths.get("TODO")); // TODO: pull the filename from somewhere
		if(ctx.hasErrors()) throw new PGoTransException(ctx.format());
		
		logger.info("Cleaning up PlusCal AST");
		Algorithm pcalAlgorithm = PlusCalConversionPass.perform(ctx, pcal);
		if(ctx.hasErrors()) throw new PGoTransException(ctx.format());
		
		logger.info("Parsing PGo annotations");
		PGoAnnotationParser annotations = AnnotationParsingPass.perform(pcal);
		
		logger.info("Checking compile options for sanity");
		CheckOptionsPass.perform(ctx, pcalAlgorithm, opts);
		if(ctx.hasErrors()) throw new PGoTransException(ctx.format());

		logger.info("Expanding PlusCal macros");
		pcalAlgorithm = PlusCalMacroExpansionPass.perform(ctx, pcalAlgorithm);
		if(ctx.hasErrors()) throw new PGoTransException(ctx.format());
		
		logger.info("Resolving TLA+ and PlusCal scoping");
		PGoScopingPass.perform(ctx, tlaModule, pcalAlgorithm, loader);
		if(ctx.hasErrors()) throw new PGoTransException(ctx.format());
		
		/*logger.info("Entering Stage One: Inferring intermediate data structures");
		PGoTransStageInitParse s1 = new PGoTransStageInitParse(pcal, opts);
		logger.info("Entering Stage Two: Parsing TLA expressions");
		PGoTransStageTLAParse s2 = new PGoTransStageTLAParse(s1);*/
		logger.info("Entering Stage Three: Inferring types");
		PGoTransStageType s3 = new PGoTransStageType(s2);
		logger.info("Entering Stage Four: Inferring atomicity constraints");
		PGoTransStageAtomicity s4 = new PGoTransStageAtomicity(s3);
		logger.info("Entering Stage Five: Generating Go AST");
		PGoTransStageGoGen s5 = new PGoTransStageGoGen(s4);
		logger.info("Entering Stage Six: Generating Go Code");
	}

	public List<String> getGoLines() {
		return null; // TODO
	}

	public void copyPackages(PGoOptions opts) throws IOException {
		FileUtils.copyDirectory(new File("src/go/pgo"), new File(opts.buildDir + "/src/pgo"));
		FileUtils.copyDirectory(new File("src/go/github.com/emirpasic"),
				new File(opts.buildDir + "/src/github.com/emirpasic"));
	}

}
