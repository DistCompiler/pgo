package pgo.checker

import pgo.model.{PGoError, SourceLocation}
import pgo.util.Description
import Description._
import pgo.util.TLAExprInterpreter.TLAValue

sealed abstract class CheckingError(override val description: Description,
                                    override val sourceLocation: SourceLocation) extends PGoError with PGoError.Error {
  override def errors: List[PGoError.Error] = List(this)
}

final case class InitialStateError(reason: Description) extends CheckingError(
  description = reason,
  sourceLocation = SourceLocation.unknown)
