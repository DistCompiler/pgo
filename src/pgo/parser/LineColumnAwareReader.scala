package pgo.parser

import pgo.util.SourceLocation

import scala.util.parsing.input.{Position, Reader}

/**
 * A generic Char reader wrapper, which counts line and column numbers within some input as it reads.
 *
 * TLA+ parsing assumes this wrapper is available, because parsing of /\ and \/ relies on knowing indentation.
 *
 * @param underlying the underlying Reader to wrap
 * @param line the current line. Either leave at its default of 0, or set this to the line
 *             from which you want to start counting.
 * @param column the current column. See above.
 */
final class LineColumnAwareCharReader(val underlying : Reader[Char], val path: java.nio.file.Path,
                                      val line : Int = 0, val column : Int = 0) extends Reader[Char] {
  override def first: Char = underlying.first

  def sourceLocation: SourceLocation = new SourceLocation(path, offset, offset, line, line, column, column)

  override def toString: String = underlying.toString

  override lazy val rest: LineColumnAwareCharReader =
    if (atEnd) {
      this
    } else {
      if (first == '\n') {
        new LineColumnAwareCharReader(underlying.rest, path, line + 1, 0)
      } else {
        new LineColumnAwareCharReader(underlying.rest, path, line, column + 1)
      }
    }

  override def pos: Position = underlying.pos
  override def atEnd: Boolean = underlying.atEnd
  override def source: CharSequence = underlying.source
  override def offset: Int = underlying.offset
}
