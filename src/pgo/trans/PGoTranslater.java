package pgo.trans;

import java.io.File;
import java.io.IOException;
import java.util.Vector;
import java.util.logging.Logger;

import org.apache.commons.io.FileUtils;

import pgo.PGoOptions;
import pgo.model.golang.GoProgram;
import pgo.parser.PGoParseException;
import pgo.parser.PcalParser.ParsedPcal;
import pgo.trans.intermediate.PGoTransStageAtomicity;
import pgo.trans.intermediate.PGoTransStageGoGen;
import pgo.trans.intermediate.PGoTransStageOne;
import pgo.trans.intermediate.PGoTransStageType;

/**
 * Performs the translation of the PlusCal AST into a Golang AST
 * 
 */
public class PGoTranslater {
	
	// The pluscal AST to be translated
	private ParsedPcal pluscal;
	
	// the translated go ast
	private GoProgram go;

	private Logger logger;

	public PGoTranslater(ParsedPcal pcal) throws PGoTransException, PGoParseException {
		this.pluscal = pcal;
		logger = Logger.getGlobal();

		logger.info("Entering Stage One: Inferring intermediate data structures");
		PGoTransStageOne s1 = new PGoTransStageOne(pcal);
		logger.info("Entering Stage Two: Inferring types");
		PGoTransStageType s2 = new PGoTransStageType(s1);
		logger.info("Entering Stage Three: Inferring atomicity constraints");
		PGoTransStageAtomicity s3 = new PGoTransStageAtomicity(s2);
		logger.info("Entering Stage Four: Generating Go AST");
		PGoTransStageGoGen s4 = new PGoTransStageGoGen(s3);
		logger.info("Entering Stage Five: Generating Go Code");
		go = s4.getGo();
	}

	public Vector<String> getLines() {
		return go.toGo();
	}

	public void copyPackages(PGoOptions opts) throws IOException {
		if (go.getImports().getImports().contains("pgoutil")) {
			FileUtils.copyDirectory(new File("src/go/pgoutil"), new File(opts.outfolder + "/src/pgoutil"));
			FileUtils.copyDirectory(new File("src/go/github.com/emirpasic"), new File(opts.outfolder + "/src/github.com/emirpasic"));
		}
	}
	
}
