package pgo.parser

import scala.util.parsing.combinator.Parsers
import scala.util.parsing.input.CharSequenceReader

trait ParsingUtils extends Parsers {
  def buildReader(path: java.nio.file.Path, seq: CharSequence): LineColumnAwareCharReader = {
    val reader = new CharSequenceReader(seq)
    val lcReader = new LineColumnAwareCharReader(reader, path)
    lcReader
  }

  def checkResult[T](result: =>ParseResult[T]): T =
    result match {
      case Success(result, _) => result
      case NoSuccess(err, in) =>
        throw ParseFailureError(err, in.asInstanceOf[LineColumnAwareCharReader].sourceLocation)
    }
}
