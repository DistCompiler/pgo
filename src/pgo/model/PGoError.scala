package pgo.model

import pgo.util.Description

abstract class PGoError extends RuntimeException {
  override def getMessage: String =
    errors.view.map(err => err.description.ensureLineBreakBefore)
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
