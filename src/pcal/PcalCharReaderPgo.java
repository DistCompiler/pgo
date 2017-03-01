package pcal;

import java.util.Vector;

import pcal.PcalCharReader;

/**
 * PlusCal package uses a non-public class PcalCharReader, which we cannot
 * include in our pgo package since non-public classes are package private. We
 * require the PcalCharReader class for parsing PlusCal files and generating the
 * AST. This class is declared in the pcal package and extends the
 * PcalCharReader, but is declared publicly so the pgo package can use the
 * class.
 *
 */

public class PcalCharReaderPgo extends PcalCharReader {

	public PcalCharReaderPgo(Vector vector, int firstLine, int firstCol, int lastLine, int lastCol) {
		super(vector, firstLine, firstCol, lastLine, lastCol);
	}

}
