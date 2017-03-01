package pgo;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Vector;
import java.util.logging.Level;
import java.util.logging.Logger;

import pcal.AST;
import pcal.IntPair;
import pcal.ParseAlgorithm;
import pcal.PcalDebug;
import pcal.PcalParams;
import pcal.PcalCharReaderPgo;
import pcal.TLAtoPCalMapping;
import pcal.exception.FileToStringVectorException;
import pcal.exception.ParseAlgorithmException;
import pcal.exception.StringVectorToFileException;
import util.ToolIO;

// TODO refactor this mess
public class PGoMain {

	/** Status indicating no errors and successful process */
	static final int STATUS_OK = 1;
	
	private static Logger logger;

    private PGoOptions opts = null;
    private static PGoMain instance = null;
	
	public PGoMain(String[] args) throws PGoOptionException {
		opts = new PGoOptions(args);
		
		// set up logging with correct verbosity
		setUpLogging(opts);
	}


	public static void main(String[] args) {
        // Get the top Logger instance
        logger = Logger.getLogger("PGoMain");
        
		try {
			instance = new PGoMain(args);
		} catch (PGoOptionException e) {
			// TODO Auto-generated catch block
			logger.severe(e.getMessage());
		}
		
		instance.run();
	}
	
	public void run() {
		if (ToolIO.getMode() == ToolIO.SYSTEM) {
			PcalDebug.reportInfo("pcal.trans Version " + PcalParams.version + " of " + PcalParams.modDate);
		}

		/*
		 * This method is called in order to make sure, that the parameters are
		 * not sticky because these are could have been initialized by the
		 * previous run
		 */
		PcalParams.resetParams();
		/*********************************************************************
		 * Get and process arguments.
		 *********************************************************************/

		/**
		 * Create the new TLAtoPCalMapping object, call it mapping here and set
		 * PcalParams.tlaPcalMapping to point to it.
		 */
		TLAtoPCalMapping mapping = new TLAtoPCalMapping();
		PcalParams.tlaPcalMapping = mapping;

		int status = STATUS_OK; // TODO fix arguments
								// parseAndProcessArguments(args);

		if (status != STATUS_OK) {
			return; // added for testing
		}

		/*********************************************************************
		 * Read the input file, and set the Vector inputVec equal to its *
		 * contents, where inputVec[i] is the string containing the contents *
		 * of line i+1 of the input file. *
		 *********************************************************************/
		Vector inputVec = null;
		try {
			inputVec = fileToStringVector(PcalParams.TLAInputFile);
		} catch (FileToStringVectorException e) {
			PcalDebug.reportError(e);
			return; // added for testing
		}

		/*********************************************************************
		 * outputVec is an alias for inputVec if the input is a .tla file, *
		 * which was not always the case in the aborted version 1.31. *
		 *********************************************************************/
		Vector outputVec = inputVec;

		/*********************************************************************
		 * Set untabInputVec to be the vector of strings obtained from *
		 * inputVec by replacing tabs with spaces. * * Tabs are date from the
		 * days when memory cost $1 per bit and are a * stupid anachronism. They
		 * should be banned. Although the various * methods taken from TLATeX
		 * should deal with tabs, there are * undoubtedly corner cases that
		 * don't work right. In particular, I * think there's one case where
		 * PcalCharReader.backspace() might be * called to backspace over a tab.
		 * It's easier to simply get rid of * the tabs than to try to make it
		 * work. * * Since the user might be evil enough to prefer tabs, with
		 * tla-file * input, the parts of the output file that are not produced
		 * by the * translator are copied from inputVec, so any tabs the user
		 * wants * are kept. *
		 *********************************************************************/
		Vector untabInputVec = removeTabs(inputVec);

		/**
		 * Look through the file for PlusCal options. They are put anywhere in
		 * the file (either before or after the module or in a comment) with the
		 * following sequence PlusCal <optional white space> options <optional
		 * white space> ( <options> )
		 * 
		 * where <options> has the same format as options on the command line.
		 */
		IntPair searchLoc = new IntPair(0, 0);
		boolean notDone = true;
		while (notDone) {
			try {
				ParseAlgorithm.FindToken("PlusCal", untabInputVec, searchLoc, "");
				String line = ParseAlgorithm.GotoNextNonSpace(untabInputVec, searchLoc);
				String restOfLine = line.substring(searchLoc.two);
				if (restOfLine.startsWith("options")) {
					// The first string after "PlusCal" not starting with a
					// space character is "options"
					if (ParseAlgorithm.NextNonIdChar(restOfLine, 0) == 7) {
						// The "options" should begin an options line
						PcalParams.optionsInFile = true;
						ParseAlgorithm.ProcessOptions(untabInputVec, searchLoc);
						notDone = false;
					}
				}
			} catch (ParseAlgorithmException e) {
				// The token "PlusCal" not found.
				notDone = false;
			}
		}

		/**
		 * translationLine is set to the line of the output file at which the \*
		 * BEGIN TRANSLATION appears--whether it is inserted into the tla-file
		 * input by the user, or inserted into the output by the translator for
		 * pcal-file input.
		 */
		int translationLine = 0;

		/*********************************************************************
		 * Set algLine, algCol to the line and column just after the string *
		 * [--]algorithm that begins the algorithm. (These are Java * ordinals,
		 * in which counting begins at 0.) * * Modified by LL on 18 Feb 2006 to
		 * use untabInputVec instead of * inputVec, to correct bug that occurred
		 * when tabs preceded the * "--algorithm". * * For the code to handle
		 * pcal-input, I introduced the use of * IntPair objects to hold <line,
		 * column> Java coordinates (counting * from zero) in a file (or an
		 * image of a file in a String Vector). * For methods that advance
		 * through the file, the IntPair object is * passed as an argument and
		 * is advanced by the method. This is * what I should have been doing
		 * from the start, but I wasn't smart * enough The IntPair curLoc is the
		 * main one used in the part of the * following code that handles
		 * pcal-file input. *
		 *********************************************************************/
		int algLine = 0;
		int algCol = -1;
		/*******************************************************************
		 * If the BEGIN/END TRANSLATION region exists, then set *
		 * translationLine to the number of the line after which the *
		 * translation is to be inserted and delete the previous version * of
		 * the translation (if it exists) from inputVec. (Line * numbering is by
		 * Java ordinals.) If the region doesn't exist, * set translationLine to
		 * -1. * * Note: we remove the previous version from inputVec, because *
		 * that's where the translated output is going to go, and also * from
		 * untabInputVec, because we will then detect if the begin * and end
		 * translation lines contain part of the algorithm within * them. *
		 *******************************************************************/
		translationLine = findTokenPair(untabInputVec, 0, PcalParams.BeginXlation1, PcalParams.BeginXlation2);
		if (translationLine != -1) {

			int endTranslationLine = findTokenPair(untabInputVec, translationLine + 1, PcalParams.EndXlation1,
					PcalParams.EndXlation2);
			if (endTranslationLine == -1) {
				PcalDebug.reportError("No line containing `" + PcalParams.EndXlation1 + " " + PcalParams.EndXlation2);
				return;
			}

			endTranslationLine = endTranslationLine - 1;
			while (translationLine < endTranslationLine) {
				inputVec.remove(endTranslationLine);
				untabInputVec.remove(endTranslationLine);
				endTranslationLine = endTranslationLine - 1;
			}
		}

		// Search for "--algorithm" or "--fair".
		// If found set algLine and algCol right after the last char,
		// set foundBegin true, and set foundFairBegin true iff it
		// was "--fair". Otherwise, set foundBegin false.
		boolean foundBegin = false;
		boolean foundFairBegin = false;
		while ((algLine < untabInputVec.size()) && !foundBegin) {
			String line = (String) untabInputVec.elementAt(algLine);
			algCol = line.indexOf(PcalParams.BeginAlg);
			if (algCol != -1) {
				algCol = algCol + PcalParams.BeginAlg.length();
				foundBegin = true;
			} else {
				algCol = line.indexOf(PcalParams.BeginFairAlg);
				if (algCol != -1) {
					// Found the "--fair". The more structurally nice thing to
					// do here would be to move past the following "algorithm".
					// However, it's easier to pass a parameter to the
					// ParseAlgorithm
					// class's GetAlgorithm method that tells it to go past the
					// "algorithm" token.
					algCol = algCol + PcalParams.BeginFairAlg.length();
					foundBegin = true;
					foundFairBegin = true;

				} else {
					algLine = algLine + 1;
				}
			}
			;
		}
		;
		if (!foundBegin) {
			PcalDebug.reportError("Beginning of algorithm string " + PcalParams.BeginAlg + " not found.");
			return; // added for testing
		}
		;

		/*
		 * Set the algColumn and algLine fields of the mapping object.
		 */
		mapping.algColumn = algCol;
		mapping.algLine = algLine;

		if (translationLine == -1) {
			/****************************************************************
			 * Insert BEGIN/END TRANSLATION comments immediately after the * end
			 * of the comment that contains the beginning of the * algorithm.
			 * Set translationLine to the (Java) line number of * the BEGIN
			 * TRANSLATION. *
			 ****************************************************************/

			// Set ecLine, ecCol to the position immediately after the
			// *) that closes the current comment.
			int depth = 1;
			int ecLine = algLine;
			int ecCol = algCol;
			boolean notFound = true;
			while (notFound && ecLine < untabInputVec.size()) {
				char[] line = ((String) untabInputVec.elementAt(ecLine)).toCharArray();

				// check current line
				while (notFound && ecCol < line.length - 1) {
					char ch = line[ecCol];
					char ch2 = line[ecCol + 1];

					if (ch == '(' && ch2 == '*') {
						// left comment delimiter
						depth++;
						ecCol = ecCol + 2;
					} else if (ch == '*' && ch2 == ')') {
						// right comment delimiter
						depth--;
						ecCol = ecCol + 2;
						if (depth == 0) {
							notFound = false;
						}
					} else {
						// not an interesting character
						ecCol++;
					}
				}

				// if not found, go to next line
				if (notFound) {
					ecLine++;
					ecCol = 0;
				}
			}

			if (notFound) {
				PcalDebug.reportError("Algorithm not in properly terminated comment");
				return; // added for testing
			}

			// Report an error if there's something else on the line that
			// doesn't begin with "\*". This is probably

			String endStuff = ((String) untabInputVec.elementAt(ecLine)).substring(ecCol).trim();

			if (!endStuff.equals("") && !endStuff.startsWith("\\*")) {
				PcalDebug.reportError(
						"Text on same line following `*)' that ends the \n   comment containing the algorithm.");
				return; // added for testing
			}
			;

			inputVec.insertElementAt("\\* BEGIN TRANSLATION", ecLine + 1);
			untabInputVec.insertElementAt("\\* BEGIN TRANSLATION", ecLine + 1);
			inputVec.insertElementAt("\\* END TRANSLATION", ecLine + 2);
			untabInputVec.insertElementAt("\\* END TRANSLATION", ecLine + 2);

			translationLine = ecLine + 1;
		}

		/*
		 * Set the mappings start line.
		 */
		mapping.tlaStartLine = translationLine + 1;

		/*********************************************************************
		 * Added by LL on 18 Feb 2006 to fix bugs related to handling of *
		 * comments. * * Remove all comments from the algorithm in
		 * untabInputVec, * replacing (* *) comments by spaces to keep the
		 * algorithm tokens * in the same positions for error reporting. *
		 *********************************************************************/
		try {
			ParseAlgorithm.uncomment(untabInputVec, algLine, algCol);
		} catch (ParseAlgorithmException e) {
			PcalDebug.reportError(e);
			return; // added for testing
		}
		// } // end else of if (PcalParams.fromPcalFile) -- i.e., end processing
		// of .tla input file.

		/*********************************************************************
		 * Set reader to a PcalCharReader for the input file (with tabs and *
		 * the previous translation removed), starting right after the *
		 * PcalParams.BeginAlg string. *
		 *********************************************************************/
		PcalCharReaderPgo reader = new PcalCharReaderPgo(untabInputVec, algLine, algCol, inputVec.size(), 0);

		/*********************************************************************
		 * Set ast to the AST node representing the entire algorithm. *
		 *********************************************************************/
		AST ast = null;
		try {
			ast = ParseAlgorithm.getAlgorithm(reader, foundFairBegin);
		} catch (ParseAlgorithmException e) {
			PcalDebug.reportError(e);
			return; // added for testing
		}
		PcalDebug.reportInfo("Parsing completed.");
		/*********************************************************************
		 * For -writeAST option, just write the file AST.tla and halt. *
		 *********************************************************************/
		if (PcalParams.WriteASTFlag) {
			WriteAST(ast);
			return; // added for testing
		}

	}

	
    public static void setUpLogging(PGoOptions opts) {
        // Set the logger's log level based on command line arguments
        if (opts.logLvlQuiet) {
            logger.setLevel(Level.WARNING);
        } else if (opts.logLvlVerbose) {
            logger.setLevel(Level.FINE);
        } else {
            logger.setLevel(Level.INFO);
        }
        return;
    }
	
	
	////////////////////////////////////////////////////////////////////////////
	// copied from pluscal
	
	/***************** METHODS FOR READING AND WRITING FILES *****************/

	/***********************************************************************
	 * Writes the Vector of strings inputVec to file named fileName, with * each
	 * element of inputVec written on a new line. *
	 ***********************************************************************/
	private static void WriteStringVectorToFile(Vector inputVec, String fileName) throws StringVectorToFileException {
		try {
			BufferedWriter fileW = new BufferedWriter(new FileWriter(fileName));
			int lineNum = 0;
			while (lineNum < inputVec.size()) {
				fileW.write((String) inputVec.elementAt(lineNum));
				fileW.newLine();
				lineNum = lineNum + 1;
			}

			fileW.close();
		} catch (Exception e) {
			throw new StringVectorToFileException("Could not write file " + fileName);
		}

	}

	/***********************************************************************
	 * Reads file fileName into a StringVector, a vector in which each * element
	 * is a line of the file. *
	 ***********************************************************************/
	private static Vector fileToStringVector(String fileName) throws FileToStringVectorException {
		Vector inputVec = new Vector(100);
		try {
			BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(new FileInputStream(fileName)));
			try {
				String nextLine = bufferedReader.readLine();
				while (nextLine != null) {
					inputVec.addElement(nextLine);
					nextLine = bufferedReader.readLine();
				}
				;
				bufferedReader.close();
			} catch (IOException e) {
				/*********************************************************
				 * Error while reading input file. *
				 *********************************************************/
				throw new FileToStringVectorException("Error reading file " + fileName + ".");
			}
		}

		catch (FileNotFoundException e) {
			/**************************************************************
			 * Input file could not be found. *
			 **************************************************************/
			throw new FileToStringVectorException("Input file " + fileName + " not found.");
		}

		return inputVec;
	}

	/**********************
	 * Writing the AST
	 ************************************/
	private static boolean WriteAST(AST ast) {
		Vector astFile = new Vector();
		astFile.addElement("------ MODULE AST -------");
		astFile.addElement("EXTENDS TLC");
		astFile.addElement("fairness == \"" + PcalParams.FairnessOption + "\"");
		astFile.addElement(" ");
		astFile.addElement("ast == ");
		astFile.addElement(ast.toString());
		astFile.addElement("==========================");
		try {
			WriteStringVectorToFile(astFile, "AST.tla");
		} catch (StringVectorToFileException e) {
			PcalDebug.reportError(e);
			return false;
		}
		PcalDebug.reportInfo("Wrote file AST.tla.");
		return true;
	}

	/********************************************************************
	 * Returns a string vector obtained from the string vector vec by *
	 * replacing any evil tabs with the appropriate number of spaces, * where
	 * "appropriate" means adding from 1 to 8 spaces in order to * make the next
	 * character fall on a column with Java column * number (counting from 0)
	 * congruent to 0 mod 8. This is what * Emacs does when told to remove tabs,
	 * which makes it good enough * for me. *
	 ********************************************************************/
	public static Vector removeTabs(Vector vec) {

		Vector newVec = new Vector();
		int i = 0;
		while (i < vec.size()) {
			String oldline = (String) vec.elementAt(i);
			String newline = "";
			int next = 0;
			while (next < oldline.length()) {
				if (oldline.charAt(next) == '\t') {
					int toAdd = 8 - (newline.length() % 8);
					while (toAdd > 0) {
						newline = newline + " ";
						toAdd = toAdd - 1;
					}
				} else {
					newline = newline + oldline.substring(next, next + 1);
				}
				;
				next = next + 1;
			}
			newVec.addElement(newline);
			i = i + 1;
		}
		;
		return newVec;
	}

	/*********************************************************************
	 * Returns the number of the first line at or after lineNum in the * vector
	 * of strings vec containing tok1 followed by 1 or more * spaces followed by
	 * tok2. Returns -1 if such a line is not found. *
	 *********************************************************************/
	private static int findTokenPair(Vector vec, int lineNum, String tok1, String tok2) {
		int i = lineNum;
		while (i < vec.size()) {
			String line = (String) vec.elementAt(i);
			int col = line.indexOf(tok1);
			int nextcol = col + tok1.length();
			if (col != -1) {
				while ((nextcol < line.length()) && (line.charAt(nextcol) == ' ')) {
					nextcol = nextcol + 1;
				}
				;
				if ((nextcol < line.length()) && (nextcol == line.indexOf(tok2))) {
					return i;
				}
			}
			;
			i = i + 1;
		}
		;
		return -1;
	}
}
