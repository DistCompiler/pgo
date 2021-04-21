package pgo.util

import scala.collection.{AbstractIterator, View, mutable}

private sealed abstract class DescriptionPart
private case object DescriptionLineBreakPart extends DescriptionPart
private case object DescriptionEnsureLineBreakPart extends DescriptionPart
private case object DescriptionIndentPart extends DescriptionPart
private case object DescriptionDedentPart extends DescriptionPart
private final case class DescriptionStringPart(str: String) extends DescriptionPart
private final case class DescriptionEmbedPart(embed: Any) extends DescriptionPart

final class Description private (private val parts: View[DescriptionPart]) {
  def indented: Description =
    new Description(View(DescriptionIndentPart) ++ parts ++ View(DescriptionDedentPart))

  def ensureLineBreakBefore: Description =
    new Description(View(DescriptionEnsureLineBreakPart) ++ parts)

  def ensureLineBreakAfter: Description =
    new Description(parts ++ View(DescriptionEnsureLineBreakPart))

  def linesIterator: Iterator[String] =
    new AbstractIterator[String] {
      private val partsIterator = parts.iterator.flatMap {
        case DescriptionEmbedPart(embed) => Description.stringToDescriptionParts(embed.toString)
        case part => Iterator.single(part)
      }
      private var atStart = true // used to detect the "first line", for ensuring leading line breaks work properly
      // note: semantically, the start of the description is at the beginning of a new line
      private var hasNewLine = true // are we at the beginning of a new line?
      private var indent = 0 // the indentation to apply after a new line, if the following line has any contents
      private val lineBuilder = new StringBuilder()
      private var nextLine: String = _

      private def gatherNextLine(): Unit = {
        nextLine = null
        while((nextLine eq null) && partsIterator.hasNext) {
          partsIterator.next() match {
            case DescriptionLineBreakPart =>
              atStart = false
              hasNewLine = true
              nextLine = lineBuilder.result()
              lineBuilder.clear()
            case DescriptionEnsureLineBreakPart =>
              if(!hasNewLine || atStart) {
                atStart = false
                hasNewLine = true
                nextLine = lineBuilder.result()
                lineBuilder.clear()
              }
            case DescriptionIndentPart =>
              indent += 2
            case DescriptionDedentPart =>
              indent -= 2
            case DescriptionStringPart(str) =>
              atStart = false
              if(hasNewLine) {
                hasNewLine = false
                (0 until indent).foreach(_ => lineBuilder += ' ')
              }
              lineBuilder.addAll(str)
            case DescriptionEmbedPart(_) => ??? // should be unreachable
          }
        }
        // lineBuilder.nonEmpty ==> make sure to output trailing strings without a new line following them
        // hasNewLine ==> make sure to output trailing new lines
        if((lineBuilder.nonEmpty || hasNewLine) && (nextLine eq null)) {
          hasNewLine = false // if a trailing new line is output, make sure we stop there
          nextLine = lineBuilder.result()
          lineBuilder.clear()
        }
      }

      gatherNextLine()

      override def hasNext: Boolean = nextLine ne null

      override def next(): String = {
        val line = nextLine
        gatherNextLine()
        line
      }
    }
}

object Description {
  private def stringToDescriptionParts(str: String): View[DescriptionPart] = {
    var i = 0
    val partsBuffer = mutable.ListBuffer[DescriptionPart]()
    val partBuilder = new StringBuilder
    while(i < str.length) {
      if(str.charAt(i) == '\n') {
        partsBuffer += DescriptionStringPart(partBuilder.result())
        partsBuffer += DescriptionLineBreakPart
        partBuilder.clear()
      } else {
        partBuilder += str.charAt(i)
      }
      i += 1
    }
    if(partBuilder.nonEmpty) {
      partsBuffer += DescriptionStringPart(partBuilder.result())
    }
    partsBuffer.result().view
  }

  implicit class IterableFlattenDescriptions(val descList: Iterable[Description]) extends AnyVal {
    def flattenDescriptions: Description =
      new Description(descList.view.flatMap(_.parts))
  }

  implicit class StringToDescription(val str: String) extends AnyVal {
    def toDescription: Description =
      new Description(stringToDescriptionParts(str))
  }

  implicit class DescriptionHelper(val ctx: StringContext) extends AnyVal {
    private def mkDesc(parts: Seq[String], args: Seq[Any]): Description = {
      val parts = Description.stringToDescriptionParts(StringContext.processEscapes(ctx.parts.head)) ++
        (args.view zip ctx.parts.view.tail).flatMap {
          case (arg, part) =>
            (arg match {
              case arg: Description => arg.parts
              case str: String => Description.stringToDescriptionParts(str)
              case any => View(DescriptionEmbedPart(any))
            }) ++ Description.stringToDescriptionParts(StringContext.processEscapes(part))
        }
      new Description(parts)
    }

    def d(args: Any*): Description = mkDesc(ctx.parts, args)

    def dd(args: Any*): Description = {
      var foundPipe = false
      val mappedParts = ctx.parts.map { part =>
        StringContext.processEscapes(part).flatMap {
          case '\n' => foundPipe = false; "\n"
          case _ if !foundPipe => ""
          case '|' => foundPipe = true; ""
          case ch => ch.toString
        }
      }
      mkDesc(mappedParts, args)
    }
  }
}
