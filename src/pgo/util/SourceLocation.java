package pgo.util;

import java.nio.file.Path;
import java.util.Objects;

public class SourceLocation implements Comparable<SourceLocation> {
	private Path file;
	private int startOffset;
	private int endOffset;
	private int startLine;
	private int endLine;
	private int startColumn;
	private int endColumn;
	
	public SourceLocation(Path file, int startOffset, int endOffset, int startLine, int endLine, int startColumn,
	                      int endColumn) {
		this.file = file;
		this.startOffset = startOffset;
		this.endOffset = endOffset;
		this.startLine = startLine;
		this.endLine = endLine;
		this.startColumn = startColumn;
		this.endColumn = endColumn;
	}
	
	public static SourceLocation unknown() {
		return new SourceLocation(null, -1, -1, -1, -1, -1, -1);
	}
	
	public boolean isUnknown() {
		return file == null;
	}
	
	public SourceLocation combine(SourceLocation other) {
		if(isUnknown()) {
			return other;
		}else if(other.isUnknown()) {
			return this;
		}
		// we assume this is programmer error, as one would usually only call this method when combining parsed
		// tokens into an AST, not later when one might reasonably combine tokens from different files
		if(!file.equals(other.getFile())) {
			throw new RuntimeException("Tried to combine source locations from two different files: " + file + ", " + other.getFile());
		}
		int mStartColumn, mEndColumn;
		if(startLine == other.getStartLine()) {
			mStartColumn = Integer.min(startColumn, other.getStartColumn());
		}else if(startLine < other.getStartLine()) {
			mStartColumn = startColumn;
		}else /* startLine > other.getStartLine() */ {
			mStartColumn = other.getStartColumn();
		}
		if(endLine == other.getEndLine()) {
			mEndColumn = Integer.max(endColumn, other.getEndColumn());
		}else if(endLine > other.getEndLine()) {
			mEndColumn = endColumn;
		}else /* endLine < other.getEndLine() */ {
			mEndColumn = other.getEndColumn();
		}
		return new SourceLocation(file,
				startOffset < other.startOffset ? startOffset : other.startOffset,
				endOffset > other.endOffset ? endOffset : other.endOffset,
				Integer.min(startLine, other.getStartLine()),
				Integer.max(endLine, other.getEndLine()),
				mStartColumn,
				mEndColumn);
	}

	public Path getFile() {
		return file;
	}

	public int getStartOffset() {
		return startOffset;
	}

	public int getEndOffset() {
		return endOffset;
	}

	public int getStartLine() {
		return startLine;
	}

	public int getEndLine() {
		return endLine;
	}

	public int getStartColumn() {
		return startColumn;
	}

	public int getEndColumn() {
		return endColumn;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + endColumn;
		result = prime * result + endLine;
		result = prime * result + ((file == null) ? 0 : file.hashCode());
		result = prime * result + startOffset;
		result = prime * result + endOffset;
		result = prime * result + startColumn;
		result = prime * result + startLine;
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		SourceLocation other = (SourceLocation) obj;
		return endColumn == other.endColumn && endLine == other.endLine && startColumn == other.startColumn &&
				startOffset == other.startOffset && endOffset == other.endOffset && startLine == other.startLine &&
				Objects.equals(file, other.file);
	}

	@Override
	public String toString() {
		if (isUnknown()) {
			return "SourceLocation [UNKNOWN]";
		} else {
			return "SourceLocation [file=" + file + ", startOffset=" + startOffset + ", endOffset=" + endOffset +
					", startLine=" + startLine + ", endLine=" + endLine + ", startColumn=" + startColumn +
					", endColumn=" + endColumn + "]";
		}
	}

	@Override
	public int compareTo(SourceLocation o) {
		if (isUnknown() && o.isUnknown()) {
			return 0;
		}
		if (isUnknown()) {
			return -1;
		}
		if (o.isUnknown()) {
			return 1;
		}
		int comparedFile = getFile().compareTo(o.getFile());
		if (comparedFile != 0) {
			return comparedFile;
		}
		int comparedStartLine = Integer.compare(getStartLine(), o.getStartLine());
		if (comparedStartLine != 0) {
			return comparedStartLine;
		}
		int comparedStartColumn = Integer.compare(getStartColumn(), o.getStartColumn());
		if (comparedStartColumn != 0) {
			return comparedStartColumn;
		}
		int comparedStartOffset = Integer.compare(getStartOffset(), o.getStartOffset());
		if (comparedStartOffset != 0) {
			return comparedStartOffset;
		}
		return Integer.compare(getEndOffset(), o.getEndOffset());
	}

}
