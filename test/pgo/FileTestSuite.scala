package pgo

import org.scalatest.funsuite.AnyFunSuite
import pgo.model.{PGoError, SourceLocationWithUnderlying}
import pgo.util.Description
import Description._
import org.scalatest

import java.util.regex.{MatchResult, Pattern}
import scala.collection.mutable

trait FileTestSuite extends AnyFunSuite {
  final lazy val goExe: String = sys.env.getOrElse("GO_EXE", "go")

  def testFiles: List[os.Path]

  def getNoMultipleWrites(file: os.Path): Boolean =
    os.exists(file / os.up / s"${file.last}.noMultipleWrites")

  def checkErrors(errors: List[PGoError.Error], testFile: os.Path): scalatest.Assertion = {
    val fileContents = os.read(testFile)
    final class ExpectedError(matchResult: MatchResult) {
      val offset: Int = locally {
        // for very, very weird cases where you can't just put the comment in the right place (e.g the place is already
        // in a comment), so you can instead bump the intended location around via [positive] character offset
        val adjustment = matchResult.group(1) match {
          case null => 0
          case offsetStr => offsetStr.tail.toInt
        }
        var offset: Int = matchResult.end()
        while(offset < fileContents.length && Character.isWhitespace(fileContents.charAt(offset))) {
          offset += 1
        }
        offset + adjustment
      }
      val name: String = matchResult.group(2)
    }

    val parenError = Pattern.compile("\\(\\*::\\s+expectedError(\\+\\d+)?:\\s+(\\w+)\\s*\\*\\)")
    val lineError = Pattern.compile("\\\\\\*::\\s+expectedError(\\+\\d+)?:\\s+(\\w+)\\s*")
    val expectedErrors = locally {
      val resultsBuilder = mutable.ListBuffer[ExpectedError]()
      parenError.matcher(fileContents).results().forEachOrdered(res => resultsBuilder += new ExpectedError(res))
      lineError.matcher(fileContents).results().forEachOrdered(res => resultsBuilder += new ExpectedError(res))
      resultsBuilder.result()
    }
    val groupedErrors = errors.groupBy(_.sourceLocation.maybeOffset)
    val groupedExpectedErrors = expectedErrors.groupBy(_.offset)

    val groupOffsets = (groupedErrors.keysIterator ++ groupedExpectedErrors.keysIterator).distinct.toArray.sortInPlace()
    val missingErrors = mutable.ListBuffer[ExpectedError]()
    val unexpectedErrors = mutable.ListBuffer[PGoError.Error]()
    val matchingErrors = mutable.ListBuffer[PGoError.Error]()
    groupOffsets.foreach { offset =>
      val expectedNames = groupedExpectedErrors.getOrElse(offset, Nil).view.map(_.name).toSet
      val actualNames = groupedErrors.getOrElse(offset, Nil).view.map(_.productPrefix).toSet
      groupedErrors.getOrElse(offset, Nil).foreach { err =>
        if(!expectedNames(err.productPrefix)) {
          unexpectedErrors += err
        } else {
          matchingErrors += err
        }
      }
      groupedExpectedErrors.getOrElse(offset, Nil).foreach { err =>
        if(!actualNames(err.name)) {
          missingErrors += err
        }
      }
    }
    if(missingErrors.nonEmpty || unexpectedErrors.nonEmpty) {
      fail {
        d"Mismatch between expected errors and actual errors.${
          if(unexpectedErrors.nonEmpty) {
            d"Unexpected errors present:${
              unexpectedErrors.view.map { err =>
                d"${err.productPrefix}(${err.sourceLocation.maybeOffset}): ${err.description} at ${err.sourceLocation.longDescription}"
                  .indented
                  .ensureLineBreakBefore
              }.flattenDescriptions
            }".ensureLineBreakBefore.indented
          } else d""
        }${
          if(missingErrors.nonEmpty) {
            d"Expected errors missing:${
              missingErrors.view.map { err =>
                d"${err.name} at ${err.offset}"
                  .indented
                  .ensureLineBreakBefore
              }.flattenDescriptions
            }".ensureLineBreakBefore.indented
          } else d""
        }${
          if(matchingErrors.nonEmpty) {
            d"Expected errors matched:${
              matchingErrors.view.map { err =>
                d"${err.productPrefix}: ${err.description} at ${err.sourceLocation.longDescription}"
                  .indented
                  .ensureLineBreakBefore
              }.flattenDescriptions
            }".ensureLineBreakBefore.indented
          } else d""
        }".linesIterator.mkString("\n")
      }
    } else {
      succeed
    }
  }
}
