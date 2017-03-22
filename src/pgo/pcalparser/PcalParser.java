package pgo.pcalparser;

import java.util.Vector;
import java.util.logging.Logger;

import pcal.AST;
import pcal.IntPair;
import pcal.ParseAlgorithm;
import pcal.PcalCharReaderPgo;
import pcal.PcalParams;
import pcal.TLAtoPCalMapping;
import pcal.exception.FileToStringVectorException;
import pcal.exception.ParseAlgorithmException;
import pgo.util.IOUtil;
import util.ToolIO;

/**
 * The pluscal parser.
 * 
 * This class takes a given pluscal file and parses it into the pluscal AST.
 *
 */
public class PcalParser {

	private Logger logger;
	// the file to parse
	private String file;
	
	public PcalParser(String file) {
		logger = Logger.getLogger("PlusCal Parser");
		this.file = file;
	}
	
	public static class ParsedPcal {
		// the list of PGo annotations
		private Vector<String> annotations;

		// the AST
		private AST ast;

		private ParsedPcal(AST ast, Vector<String> annotations) {
			this.ast = ast;
			this.annotations = annotations;
		}

		public Vector<String> getPGoAnnotations() {
			return annotations;
		}

		public AST getAST() {
			return ast;
		}
	}
	
	public ParsedPcal parse() throws PcalParseException {
		if (ToolIO.getMode() == ToolIO.SYSTEM) {
			logger.info("pcal.trans Version " + PcalParams.version + " of " + PcalParams.modDate);
		}

		/*
		 * This method is called in order to make sure, that the parameters are
		 * not sticky because these are could have been initialized by the
		 * previous run
		 */
		PcalParams.resetParams();
		
		// TODO refactor below into parser then make conversion
		// PcalParser parse = new PcalParser();
		
		/*********************************************************************
		 * Get and process arguments.
		 *********************************************************************/

		/**
		 * Create the new TLAtoPCalMapping object, call it mapping here and set
		 * PcalParams.tlaPcalMapping to point to it.
		 */
		TLAtoPCalMapping mapping = new TLAtoPCalMapping();
		PcalParams.tlaPcalMapping = mapping;

		/*********************************************************************
		 * Read the input file, and set the Vector inputVec equal to its *
		 * contents, where inputVec[i] is the string containing the contents *
		 * of line i+1 of the input file. *
		 *********************************************************************/
		Vector inputVec = null;
		try {
			inputVec = IOUtil.fileToStringVector(file);
		} catch (FileToStringVectorException e) {
			throw new PcalParseException(e.getMessage());
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

		}

		if (!foundBegin) {
			throw new PcalParseException("Beginning of algorithm string " + PcalParams.BeginAlg + " not found.");
		}
		
        /*
         * Set the algColumn and algLine fields of the mapping object.
         */
        mapping.algColumn = algCol;
        mapping.algLine = algLine;

		/*********************************************************************
		 * Added by LL on 18 Feb 2006 to fix bugs related to handling of *
		 * comments. * * Remove all comments from the algorithm in
		 * untabInputVec, * replacing (* *) comments by spaces to keep the
		 * algorithm tokens * in the same positions for error reporting. *
		 *********************************************************************/
		Vector<String> annotations = findPGoAnnotations(untabInputVec);
		try {
			ParseAlgorithm.uncomment(untabInputVec, algLine, algCol);
		} catch (ParseAlgorithmException e) {
			throw new PcalParseException(e.getMessage());
		}

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
			throw new PcalParseException(e.getMessage());
		}
		logger.info("Parsing completed.");

		return new ParsedPcal(ast, annotations);
	}
	
	/**
	 * Finds all comments that are pgo annotations PGo annotations are comments
	 * of format "@PGo <string> @PGo" on one line
	 * 
	 * @param untabInputVec
	 * @return the parsed go annotations
	 */
	private Vector<String> findPGoAnnotations(Vector untabInputVec) {
		Vector<String> annotations = new Vector<String>();
		for (String line : (Vector<String>) untabInputVec) {
			boolean isComment = false;
			boolean isPGo = false;
			StringBuilder sb = null;
			for (int i = 0; i < line.length(); ++i) {
				char c = line.charAt(i);
				if (!isComment) {
					if (c == '(') {
						if (i + 1 < line.length() && line.charAt(i + 1) == '*') {
							isComment = true;
						}
					} else if (c == '\\') {
						if (i + 1 < line.length() && line.charAt(i + 1) == '*') {
							isComment = true;

						}
					}
					if (isComment) {
						++i;
						while (i + 1 < line.length() && line.charAt(++i) == '*') {
						}
					}
				} else if (isPGo) {
					if (c == '@') {
						if (i + 3 < line.length() && line.charAt(i + 1) == 'P' && line.charAt(i + 2) == 'G'
								&& line.charAt(i + 3) == 'o') {
							isPGo = false;
							i += 3;
							annotations.add(sb.toString());
							continue;
						}
					}
					sb.append(c);
				} else if (!isPGo && isComment) {
					if (c == '@') {
						if (i + 3 < line.length() && line.charAt(i + 1) == 'P' && line.charAt(i + 2) == 'G'
								&& line.charAt(i + 3) == 'o') {
							isPGo = true;
							i += 3;
							sb = new StringBuilder();
						}
					} else if (c == '*') {
						if (i + 1 < line.length() && line.charAt(i + 1) == ')') {
							isComment = false;
						}
					}
				}
			}
		}
		return annotations;
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
