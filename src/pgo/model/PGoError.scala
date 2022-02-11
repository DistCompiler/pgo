package pgo.model

import pgo.util.Description

import Description._

abstract class PGoError extends RuntimeException {
  override def getMessage: String =
    errors.view.map { err =>
      val locDesc =
        if(err.sourceLocation ne SourceLocation.unknown) {
          d" at ${err.sourceLocation.longDescription}"
        } else {
          d""
        }

      d"${err.description}$locDesc".ensureLineBreakBefore
    }
      .flattenDescriptions
      .linesIterator
      .mkString("\n")

  def errors: List[PGoError.Error]
}

object PGoError {
  trait Error {
    def sourceLocation: SourceLocation
    def description: Description
    def productPrefix: String
  }
}
