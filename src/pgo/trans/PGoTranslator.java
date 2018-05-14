package pgo.trans;

import org.apache.commons.io.FileUtils;
import pgo.PGoNetOptions;
import pgo.PGoOptions;
import pgo.model.golang.GoProgram;
import pgo.parser.PGoParseException;
import pgo.parser.PcalParser.ParsedPcal;
import pgo.trans.intermediate.*;

import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.logging.Logger;

/**
 * Performs the translation of the PlusCal AST into a Golang AST
 * 
 */
public class PGoTranslator {
	// the translated go ast
	private GoProgram go;

	public PGoTranslator(ParsedPcal pcal, PGoNetOptions opts) throws PGoTransException, PGoParseException {
		Logger logger = Logger.getGlobal();

		logger.info("Entering Stage One: Inferring intermediate data structures");
		PGoTransStageInitParse s1 = new PGoTransStageInitParse(pcal, opts);
		logger.info("Entering Stage Two: Parsing TLA expressions");
		PGoTransStageTLAParse s2 = new PGoTransStageTLAParse(s1);
		logger.info("Entering Stage Three: Inferring types");
		PGoTransStageType s3 = new PGoTransStageType(s2);
		logger.info("Entering Stage Four: Inferring atomicity constraints");
		PGoTransStageAtomicity s4 = new PGoTransStageAtomicity(s3);
		logger.info("Entering Stage Five: Generating Go AST");
		PGoTransStageGoGen s5 = new PGoTransStageGoGen(s4);
		logger.info("Entering Stage Six: Generating Go Code");
		go = s5.getGo();
	}

	public List<String> getGoLines() {
		return go.toGo();
	}

	public void copyPackages(PGoOptions opts) throws IOException {
		FileUtils.copyDirectory(new File("src/go/pgo"), new File(opts.buildDir + "/src/pgo"));
		FileUtils.copyDirectory(new File("src/go/github.com/emirpasic"),
				new File(opts.buildDir + "/src/github.com/emirpasic"));
	}

}
