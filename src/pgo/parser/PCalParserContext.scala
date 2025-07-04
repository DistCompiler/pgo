package pgo.parser

import pgo.model.pcal._
import pgo.model.Definition
import pgo.model.tla.TLAIdentifier

final case class PCalParserContext()(using val ctx: TLAParserContext) {
  def withDefinition(defn: Definition): PCalParserContext =
    copy()(using ctx.withDefinition(defn))

  def withProcessSelf(self: PCalVariableDeclarationBound): PCalParserContext =
    copy()(using
      ctx.copy(
        currentScope = ctx.currentScope.updated(
          Definition.ScopeIdentifierName(
            TLAIdentifier("self").setSourceLocation(self.sourceLocation),
          ),
          self,
        ),
      ),
    )

  def withLateBinding: PCalParserContext =
    copy()(using ctx.withLateBinding)
}

object PCalParserContext {
  given getTLAParserContext(using
      ctx: PCalParserContext,
  ): TLAParserContext = ctx.ctx
}
