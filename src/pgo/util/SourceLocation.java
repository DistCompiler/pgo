package pgo.util;

import java.nio.file.Path;

public class SourceLocation {
	
	Path file;
	int startLine;
	int endLine;
	int startColumn;
	int endColumn;
	
	public SourceLocation(Path file, int startLine, int endLine, int startColumn, int endColumn) {
		this.file = file;
		this.startLine = startLine;
		this.endLine = endLine;
		this.startColumn = startColumn;
		this.endColumn = endColumn;
	}
	
	public SourceLocation combine(SourceLocation other) {
		// we assume this is programmer error, as one would usually only call this method when combining parsed
		// tokens into an AST, not later when one might reasonably combine tokens from different files
		if(!file.equals(other.getFile())) {
			throw new RuntimeException("Tried to combine source locations from two different files: " + file + ", " + other.getFile());
		}
		return new SourceLocation(file,
				Integer.min(startLine, other.getStartLine()),
				Integer.max(endLine, other.getEndLine()),
				Integer.min(startColumn, other.getStartColumn()),
				Integer.max(endColumn, other.getEndColumn()));
	}

	public Path getFile() {
		return file;
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
	
}
