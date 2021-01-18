package pgo.util;

import pgo.Unreachable;
import pgo.formatters.IndentingWriter;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.RandomAccessFile;
import java.io.StringWriter;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.StandardCharsets;
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

	public String prettyString() {
		StringWriter sw = new StringWriter();
		writePretty(new IndentingWriter(sw));
		return sw.getBuffer().toString();
	}

	public void writePretty(IndentingWriter out) {
		try {
			if(isUnknown()) {
				out.write("at unknown source location");
			} else {
				out.write("at ");
				if(startLine != endLine) {
					out.write(""+(startLine+1)+":"+(startColumn+1)+"-"+(endLine+1)+":"+endColumn);
				} else {
					if(startColumn != endColumn) {
						out.write(""+(startLine+1)+":"+(startColumn+1)+"-"+endColumn);
					} else {
						out.write(""+(startLine+1)+":"+(startColumn+1));
					}
				}
				out.write(" in file "+file);
				out.newLine();
				try {
					FileChannel fileChannel = new RandomAccessFile(file.toFile(), "r").getChannel();
					MappedByteBuffer buffer = fileChannel.map(FileChannel.MapMode.READ_ONLY, 0, fileChannel.size());
					CharSequence charSeq = StandardCharsets.UTF_8.decode(buffer);
					int lineStart = startOffset;
					while(lineStart >= 0 && (lineStart >= charSeq.length() || charSeq.charAt(lineStart) != '\n')) {
						lineStart--;
					}
					if(charSeq.charAt(lineStart) == '\n') {
						lineStart++;
					}
					int lineEnd = endOffset;
					while(lineEnd < charSeq.length() && charSeq.charAt(lineEnd) != '\n') {
						lineEnd++;
					}
					if(startLine != endLine) {
						for(int pos = lineStart; pos < startOffset; pos++) {
							out.append(' ');
						}
						for(int pos = startOffset; pos <= endOffset && charSeq.charAt(pos) != '\n'; pos++) {
							out.append('v');
						}
						out.newLine();
					}
					int lastLineBegin = lineStart;
					for(int pos = lineStart; pos < lineEnd; pos++) {
						if(charSeq.charAt(pos) == '\n') {
							lastLineBegin = pos + 1;
						}
					}
					out.append(charSeq, lineStart, lineEnd);
					out.newLine();
					for(int pos = lastLineBegin; pos < startOffset; pos++) {
						out.append(' ');
					}
					final int effectiveEndOffset;
					if(startOffset == endOffset) {
						effectiveEndOffset = endOffset + 1;
					} else {
						effectiveEndOffset = endOffset;
					}
					for(int pos = startOffset; pos < lineEnd && pos < effectiveEndOffset; pos++) {
						out.append('^');
					}
					if(startOffset == charSeq.length()) {
						out.append("^ EOF");
					}
				} catch (IOException e) { // if we can't read the file, replace the intended message with stacktrace
					PrintWriter pw = new PrintWriter(out);
					e.printStackTrace(pw);
				}
			}
		} catch (IOException e) {
			throw new Unreachable(); // string ops shouldn't throw IO exceptions
		}
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
