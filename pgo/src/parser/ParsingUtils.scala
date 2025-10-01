package pgo.parser

import scala.util.parsing.combinator.Parsers
import scala.util.parsing.input.CharSequenceReader

import pgo.model.SourceLocation

trait ParsingUtils extends Parsers {
  def buildReader(
      seq: CharSequence,
      underlyingText: SourceLocation.UnderlyingText,
  ): LineColumnAwareCharReader = {
    val reader = new CharSequenceReader(seq)
    val lcReader = new LineColumnAwareCharReader(reader, underlyingText)
    lcReader
  }

  def checkResult[T](result: => ParseResult[T]): T =
    (result: @unchecked) match {
      case Success(result, _) => result
      case NoSuccess(err, in) =>
        throw ParseFailureError(
          err,
          in.asInstanceOf[LineColumnAwareCharReader].currentSourceLocation,
        )
    }
}
