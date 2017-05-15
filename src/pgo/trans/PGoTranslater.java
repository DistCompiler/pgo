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
		PGoTransStageOne.init(pcal);
		logger.info("Entering Stage Two: Inferring types");
		PGoTransStageType.init(PGoTransStageOne.instance);
		logger.info("Entering Stage Three: Inferring atomicity constraints");
		PGoTransStageAtomicity.init(PGoTransStageType.instance);
		logger.info("Entering Stage Four: Generating Go AST");
		PGoTransStageGoGen.init(PGoTransStageAtomicity.instance);
		logger.info("Entering Stage Five: Generating Go Code");
		go = PGoTransStageGoGen.instance.getGo();
	}

	public Vector<String> getLines() {
		return go.toGo();
	}

	public void copyPackages(PGoOptions opts) throws IOException {
		if (go.getImports().getImports().contains("mapset")) {
			FileUtils.copyDirectory(new File("src/go/mapset"), new File(opts.outfolder + "/src/mapset"));
		}
		if (go.getImports().getImports().contains("pgoutil")) {
			FileUtils.copyDirectory(new File("src/go/pgoutil"), new File(opts.outfolder + "/src/pgoutil"));
		}
	}
	
}
