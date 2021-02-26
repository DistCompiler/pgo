package pgo.trans.passes.constdef

import pgo.PGoConstantDef
import pgo.errors.Issue
import pgo.errors.IssueContext
import pgo.model.tla.TLAExpression
import pgo.parser._
import pgo.trans.passes.parse.ParsingIssue

import java.util
import scala.jdk.CollectionConverters._

object ConstantDefinitionParsingPass {
  @throws[Issue]
  def perform(defs: util.Map[String, PGoConstantDef]): util.HashMap[String, TLAExpression] = {
    val result = new util.HashMap[String, TLAExpression]
    defs.asScala.iterator.toList.sortBy(_._1).foreach {
      case (key, defn) =>
        try {
          val expr = TLAParser.readExpression(defn.location.getFile, defn.contents)
          result.put(key, expr)
        } catch {
          case e: ParseFailureError =>
            throw new ParsingIssue("config", e)
        }
    }
    result
  }
}