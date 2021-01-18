package pgo.parser

import com.github.difflib.{DiffUtils, UnifiedDiffUtils}
import org.scalatest.Assertions
import scala.util.parsing.combinator.RegexParsers

import scala.jdk.CollectionConverters._
import scala.util.parsing.input.CharSequenceReader

trait TLAParserTestUtils extends Assertions with RegexParsers {
  def testParserOutput[T](input: String, p: Parser[T], expected: T) = {
    val path = java.nio.file.Paths.get("test")
    val reader = new CharSequenceReader(input)
    val lcReader = new LineColumnAwareCharReader(reader, path)
    phrase(p)(lcReader) match {
      case Success(actual, _) =>
        if(actual != expected) {
          val expectedLines = expected.toString.linesIterator.toList
          val patch = DiffUtils.diff(expectedLines.asJava, actual.toString.linesIterator.toList.asJava)
          val diff = UnifiedDiffUtils.generateUnifiedDiff("expected", "actual", expectedLines.asJava, patch, 3)
          val diffStr = diff.asScala.mkString("\n")
          fail(s"unexpected parse result, diff:\n$diffStr")
        }
      case ns @ NoSuccess(err, restInput) =>
        fail(s"${restInput.pos.longString}\n$err")
    }
  }
}
