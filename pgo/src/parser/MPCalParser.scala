package pgo.parser

import scala.collection.mutable

import pgo.model.Definition.ScopeIdentifier
import pgo.model.mpcal.*
import pgo.model.pcal.*
import pgo.model.tla.*
import pgo.model.{
  Definition,
  SourceLocatable,
  SourceLocation,
  SourceLocationWithUnderlying,
  Visitable,
}
import pgo.parser.MPCalParserContext.given
import pgo.parser.PCalParserContext.given
import pgo.util.!!!

trait MPCalParser extends PCalParser {

  private def cast[T](p: MPCalParser#Parser[T]): Parser[T] =
    // You might think that a typecast is ok here, and you'd be right in (some versions of?)
    // Scala 2.x because owner-checks were being elided and the matching could not distinguish
    // between this.Failure or that.Success. Scala 3 gets the path-dependent types right
    // at runtime, so we have to translate between path-dependent result types.
    // Note: while this is self-inflicted due to wanting multiple versions of MPCalParser,
    //       the fact that doing this duplicates all the result types is not ideal, and makes the cake
    //       pattern less attractive for designing robust parser combinator APIs.
    new Parser[T]:
      def apply(in: Input): ParseResult[T] =
        p.apply(in) match
          case success: MPCalParser#Success[T] =>
            Success(success.result, success.next)
          case failure: MPCalParser#Failure =>
            Failure(failure.msg, failure.next)
          case error: MPCalParser#Error => Error(error.msg, error.next)

  def mpcalRefSuffix: Parser[Int] =
    "^" ^^^ -1 | repsep("[" ~> ws ~> "_" ~> ws ~> "]", ws).map(_.length)

  def mpcalParam(using ctx: MPCalParserContext): Parser[MPCalParam] =
    withSourceLocation {
      "ref" ~> ws ~> tlaIdentifierExpr ~ (ws ~> mpcalRefSuffix) ^^ {
        case id ~ mappingCount => MPCalRefParam(id, mappingCount)
      } |
        (tlaIdentifierExpr <~ ws) ^^ MPCalValParam.apply
    }

  def mpcalArchetype(using ctx: MPCalParserContext): Parser[MPCalArchetype] =
    withSourceLocation {
      val origCtx = ctx
      ("archetype" ~> ws ~> tlaIdentifierExpr ~ (ws ~> "(" ~> ws ~> repsep(
        mpcalParam,
        ws ~> "," ~> ws,
      ) <~ ws <~ ")")).flatMap { case name ~ params =>
        val self = TLAIdentifier("self")
          .setSourceLocation(name.sourceLocation)
          .toDefiningIdentifier
        given ctx: MPCalParserContext =
          params.foldLeft(origCtx.withDefinition(self))(_.withDefinition(_))
        val origCtx2 = ctx
        opt(ws ~> pcalVarDecls).flatMap { declsOpt =>
          given ctx: MPCalParserContext =
            declsOpt.getOrElse(Nil).foldLeft(origCtx2)(_.withDefinition(_))
          (ws ~> pcalCSyntax.pcalCompoundStmt) ^^ ((
            name,
            self,
            params,
            declsOpt.getOrElse(Nil),
            _,
          ))
        }
      } ^^ { case (name, self, params, decls, body) =>
        MPCalArchetype(name, self, params, decls, body)
      }
    }

  val mpcalMappingPosition: Parser[Int] =
    regex("""[1-9]\d*""".r).map(_.toInt)
  def mpcalMapping(positionMappings: Map[String, Int], maxPosition: Int)(using
      ctx: MPCalParserContext,
  ): Parser[MPCalMapping] =
    withSourceLocation {
      "mapping" ~> ws ~> {
        withSourceLocation {
          tlaIdentifierExpr ~ (ws ~> mpcalRefSuffix) ^^ {
            case id ~ mappingCount =>
              positionMappings.get(id.id) match {
                case None => throw MappingLookupError(id)
                case Some(position) =>
                  MPCalMappingTarget(position, mappingCount)
              }
          }
        } |
          withSourceLocation {
            querySourceLocation(
              "@" ~> mpcalMappingPosition,
            ) ~ (ws ~> mpcalRefSuffix) ^^ {
              case (positionLoc, position) ~ mappingCount =>
                if (position > maxPosition || position <= 0) {
                  throw MappingIndexOutOfBounds(
                    positionLoc,
                    position,
                    maxPosition,
                  )
                }
                MPCalMappingTarget(position - 1, mappingCount)
            }
          }
      } ~ (ws ~> "via" ~> ws ~> tlaIdentifierExpr) ^^ {
        case target ~ mappingMacroIdentifier =>
          ctx.mappingMacros.get(mappingMacroIdentifier) match {
            case None => throw MappingMacroLookupError(mappingMacroIdentifier)
            case Some(mappingMacro) =>
              val result = MPCalMapping(target, mappingMacroIdentifier)
              result.setRefersTo(mappingMacro)
              result
          }
      }
    }

  def mpcalInstance(using ctx: MPCalParserContext): Parser[MPCalInstance] =
    withSourceLocation {
      val origCtx = ctx
      (((("fair" ~> ws ~> "+" ^^^ PCalFairness.StrongFair) | ("fair" ^^^ PCalFairness.WeakFair) | success(
        PCalFairness.Unfair,
      )) ~
        (ws ~> "process" ~> ws ~> "(" ~> pcalVarDeclBound <~ ws <~ ")"))
        .flatMap { case fairness ~ nameDecl =>
          given ctx: MPCalParserContext =
            origCtx.withDefinition(nameDecl)
          ((ws ~> "==" ~> ws ~> "instance" ~> ws ~> tlaIdentifierExpr) ~
            (ws ~> "(" ~> ws ~> repsep(
              mpcalParamExpr ^^ {
                case TLAExtensionExpression(pExp: MPCalRefExpr) => Left(pExp)
                case expr: TLAExpression                        => Right(expr)
              },
              ws ~> "," ~> ws,
            ) <~ ws <~ ")")) ^^ { parts => (fairness, nameDecl, parts) }
        })
        .flatMap { case (fairness, nameDecl, target ~ arguments) =>
          val namePosMapping = arguments.view.zipWithIndex.collect {
            case (Left(param), idx) => param.name.id -> idx
          }.toMap
          ws ~> repsep(
            mpcalMapping(namePosMapping, arguments.size),
            ws,
          ) <~ ws <~ ";" ^^ { mappings =>
            ctx.archetypes.get(target) match {
              case None => throw ArchetypeLookupError(target)
              case Some(archetype) =>
                val result =
                  MPCalInstance(nameDecl, fairness, target, arguments, mappings)
                result.setRefersTo(archetype)
                result
            }
          }
        }
    }

  def mpcalYield(using
      ctx: PCalParserContext,
  ): Parser[PCalExtensionStatement] =
    withSourceLocation {
      withSourceLocation {
        "yield" ~> ws ~>! tlaExpression ^^ MPCalYield.apply
      } ^^ PCalExtensionStatement.apply
    }

  object mpcalMappingMacroBody extends MPCalParser {
    def mpcalSpecialVariable(using
        ctx: TLAParserContext,
    ): Parser[TLAExpression] =
      withSourceLocation {
        withSourceLocation {
          "$variable" ^^ (_ => MPCalDollarVariable()) |
            "$value" ^^ (_ => MPCalDollarValue())
        } ^^ TLAExtensionExpression.apply
      }

    override def tlaExpressionNoOperators(using
        ctx: TLAParserContext,
    ): Parser[TLAExpression] =
      mpcalSpecialVariable | super.tlaExpressionNoOperators

    override def pcalLhsId(using
        ctx: PCalParserContext,
    ): Parser[PCalAssignmentLhs] =
      withSourceLocation(
        withSourceLocation(
          "$variable" ^^ (_ => MPCalDollarVariable()),
        ) ^^ PCalAssignmentLhsExtension.apply,
      ) |
        super.pcalLhsId

    override val pcalCSyntax: PCalCSyntax = new PCalCSyntax {
      override def pcalUnlabeledStmt(using
          ctx: PCalParserContext,
      ): Parser[PCalStatement] =
        mpcalYield | super.pcalUnlabeledStmt
    }
  }

  def mpcalMappingMacro(using
      ctx: MPCalParserContext,
  ): Parser[MPCalMappingMacro] =
    withSourceLocation {
      val origCtx = ctx
      querySourceLocation("mapping" ~> ws ~> "macro" ~> ws ~> tlaIdentifierExpr)
        .flatMap { case (selfLoc, name) =>
          val selfDecl = TLAIdentifier("self")
            .setSourceLocation(selfLoc)
            .toDefiningIdentifier
          given ctx: MPCalParserContext =
            origCtx.withDefinition(selfDecl)
          (ws ~> "{" ~> ws ~> "read" ~> ws ~> cast(
            mpcalMappingMacroBody.pcalCSyntax.pcalCompoundStmt,
          )) ~
            (ws ~> "write" ~> ws ~> cast(
              mpcalMappingMacroBody.pcalCSyntax.pcalCompoundStmt,
            ) <~ ws <~ "}") ^^
            ((name, selfDecl, _))
        } ^^ { case (name, selfDecl, readBlock ~ writeBlock) =>
        MPCalMappingMacro(name, selfDecl, readBlock, writeBlock)
      }
    }

  def mpcalProcedure(using ctx: MPCalParserContext): Parser[MPCalProcedure] =
    withSourceLocation {
      val origCtx = ctx
      querySourceLocation("procedure" ~> ws ~> tlaIdentifierExpr).flatMap {
        case (selfLoc, id) =>
          val selfDecl = TLAIdentifier("self")
            .setSourceLocation(selfLoc)
            .toDefiningIdentifier
          given ctx: MPCalParserContext =
            origCtx.withDefinition(selfDecl)
          val origCtx2 = ctx
          ((ws ~> "(" ~> ws ~> repsep(mpcalParam, ws ~> "," ~> ws)) ~
            (ws ~> ")" ~> opt(
              ws ~> ("variables" | "variable") ~> ws ~> rep1sep(
                pcalPVarDecl,
                ws ~> (";" | ",") ~> ws,
              ) <~ opt(ws ~> (";" | ",")),
            ).map(_.getOrElse(Nil))))
            .flatMap { case args ~ locals =>
              given ctx: MPCalParserContext = locals.foldLeft(
                args.foldLeft(origCtx2)(_.withDefinition(_)),
              )(_.withDefinition(_))
              (ws ~> cast(mpcalWithRefs.pcalCSyntax.pcalCompoundStmt) <~ opt(
                ws ~> ";",
              )) ^^ ((id, selfDecl, args, locals, _))
            }
      } ^^ { case (id, selfDecl, args, locals, body) =>
        MPCalProcedure(id, selfDecl, args, locals, body)
      }
    }

  def mpcalParamExpr(using ctx: PCalParserContext): Parser[TLAExpression] =
    withSourceLocation {
      querySourceLocation {
        "ref" ~> ws ~> tlaIdentifierExpr ~ (ws ~> mpcalRefSuffix) ^^ {
          case id ~ mappingCount => (id, MPCalRefExpr(id, mappingCount))
        }
      }
        .map { case (loc, (id, ref)) =>
          ref.setSourceLocation(loc)
          ctx.ctx.lookupDefinition(
            List(Definition.ScopeIdentifierName(id)),
          ) match {
            case None =>
              if (ctx.ctx.lateBindingStack > 0) {
                // pass; expect whoever incremented late bindings to set the reference later
              } else {
                throw DefinitionLookupError(
                  Nil,
                  Definition.ScopeIdentifierName(id),
                )
              }
            case Some(defn) =>
              ref.setRefersTo(defn)
          }
          ref
        }
        .map(TLAExtensionExpression.apply)
    } | super.pcalCallParam

  def mpcalWithRefs(using ctx: MPCalParserContext): MPCalParser =
    new MPCalParser {
      override def pcalCallParam(using
          ctx: PCalParserContext,
      ): Parser[TLAExpression] = mpcalParamExpr
    }

  def mpcalBlock(using ctx: MPCalParserContext): Parser[MPCalBlock] =
    withSourceLocation {
      val origCtx = ctx.withLateBinding
      (("--mpcal" ~> ws ~> tlaIdentifierExpr <~ ws <~ "{") ~ opt(
        ws ~> pcalDefinitions,
      ).map(_.getOrElse(Nil))).flatMap { case name ~ defns =>
        given ctx: MPCalParserContext =
          defns.foldLeft(origCtx)((ctx, unit) =>
            unit.definitions.foldLeft(ctx)(_.withDefinition(_)),
          )
        val origCtx2 = ctx
        ((ws ~> repsep(cast(mpcalWithRefs.pcalCSyntax.pcalMacro), ws)) ~
          (ws ~> repsep(cast(mpcalWithRefs.mpcalProcedure), ws)) ~
          (ws ~> repsep(cast(mpcalWithRefs.mpcalMappingMacro), ws)) ~
          (ws ~> repsep(cast(mpcalWithRefs.mpcalArchetype), ws)) ~
          opt(ws ~> pcalVarDecls).map(_.getOrElse(Nil))).flatMap {
          case macros ~ mpcalProcedures ~ mappingMacros ~ archetypes ~ varDecls =>
            given ctx: MPCalParserContext = {
              val tmp1 = archetypes.foldLeft(origCtx2)(_.withArchetype(_))
              val tmp2 = varDecls.foldLeft(tmp1)(_.withDefinition(_))
              mappingMacros.foldLeft(tmp2)(_.withMappingMacro(_))
            }
            (ws ~> repsep(mpcalInstance, ws)) ~
              (ws ~> repsep(
                cast(mpcalWithRefs.pcalCSyntax.pcalProcedure),
                ws,
              )) ~ {
                (ws ~> cast(
                  mpcalWithRefs.pcalCSyntax.pcalCompoundStmt,
                )) ^^ (Left(_)) |
                  (ws ~> repsep(
                    cast(mpcalWithRefs.pcalCSyntax.pcalProcess),
                    ws,
                  )) ^^ (Right(_))
              } <~ ws <~ "}" ^^ ((
                name,
                defns,
                macros,
                mpcalProcedures,
                mappingMacros,
                archetypes,
                varDecls,
                _,
              ))
        }
      } ^^ {
        case (
              name,
              defns,
              macros,
              mpcalProcedures,
              mappingMacros,
              archetypes,
              varDecls,
              instances ~ pcalProcedures ~ procs,
            ) =>
          val dummyPCalProc =
            PCalProcedure(
              TLAIdentifier("dummy"),
              TLAIdentifier("self").toDefiningIdentifier,
              Nil,
              Nil,
              Nil,
            ) // a dummy PCal procedure to make auto-rename happy, see below
          var result = MPCalBlock(
            name,
            defns,
            macros,
            mpcalProcedures,
            mappingMacros,
            archetypes,
            varDecls,
            instances,
            dummyPCalProc :: pcalProcedures,
            procs,
          )
          val macroMap = macros.view.map(m => m.name -> m).toMap
          result.visit() { case call @ PCalMacroCall(target, _) =>
            macroMap.get(target) match {
              case Some(m) => call.setRefersTo(m)
              case None    => throw MacroLookupError(target)
            }
          }
          val mpcalProcedureMap =
            mpcalProcedures.view.map(proc => proc.name -> proc).toMap
          val pcalProcedureMap = pcalProcedures.view
            .map((proc: PCalProcedure) => proc.name -> proc)
            .toMap
          result.visit() { case call @ PCalCall(target, _) =>
            pcalProcedureMap.get(target) match {
              case Some(procedure) => call.setRefersTo(procedure)
              case None if mpcalProcedureMap.contains(target) =>
                // dummy value, whole AST node is replaced below
                call.setRefersTo(dummyPCalProc)
              case None => throw ProcedureLookupError(target)
            }
          }

          // resolve bleeding refs, but refuse to resolve ambiguous refs, where a bleed could go to one of multiple locals
          val bleedableDefs = result.bleedableDefinitions.toList
          val bleedableDefNamesSeen = mutable.HashSet[ScopeIdentifier]()
          val bleedableDefsWithDups = bleedableDefs.iterator.flatMap { defn =>
            if (bleedableDefNamesSeen(defn.identifier)) {
              Some(defn.identifier)
            } else {
              bleedableDefNamesSeen += defn.identifier
              Nil
            }
          }.toSet
          ctx.ctx.ctx.resolveLateBindings(
            result,
            bleedableDefs.filter(defn =>
              !bleedableDefsWithDups(defn.identifier),
            ),
          )

          // rewrite pcal proc calls to mpcal proc calls strictly at the end, to avoid messing up the auto-renaming in rewrite
          // like this, even if it's fake, all the parts have a refersTo, and the auto-renaming at least "thinks" it's working correctly
          result = result.rewrite() {
            case call @ PCalCall(target, args)
                if mpcalProcedureMap.contains(target) =>
              val transformedArgs = args.map {
                case TLAExtensionExpression(pExp: MPCalRefExpr) => Left(pExp)
                case expr                                       => Right(expr)
              }
              PCalExtensionStatement(
                MPCalCall(target, transformedArgs)
                  .setSourceLocation(call.sourceLocation)
                  .setRefersTo(mpcalProcedureMap(target)),
              ).setSourceLocation(call.sourceLocation)
          }
          // now the rewrite is done, drop the dummy PCal proc, which should have no more references
          val stableResult = result
          stableResult.decorateLike(
            stableResult
              .copy(pcalProcedures = result.pcalProcedures.tail)
              .asInstanceOf[stableResult.type],
          )
      }
    }
}

object MPCalParser extends MPCalParser with ParsingUtils {
  def hasMPCalBlock(
      underlying: SourceLocation.UnderlyingText,
      charSeq: CharSequence,
  ): Boolean =
    findInComment("mpcal", "--mpcal")(buildReader(charSeq, underlying)) match {
      case Success(_, _)   => true
      case NoSuccess(_, _) => false
      case _ =>
        !!! // keep scalac quiet; NoSuccess(_, _) really does cover the two other cases!
    }

  def readBlock(
      underlying: SourceLocation.UnderlyingText,
      charSeq: CharSequence,
      tlaModule: TLAModule,
  ): MPCalBlock = {
    given tlaCtx: TLAParserContext =
      tlaModule
        .moduleDefinitions(captureLocal = true)
        .foldLeft(
          BuiltinModules.Intrinsics.members
            .foldLeft(TLAParserContext(underlying))(_.withDefinition(_)),
        )(_.withDefinition(_))
    given pcalCtx: PCalParserContext = PCalParserContext()
    given ctx: MPCalParserContext = MPCalParserContext()
    val result = checkResult(
      phrase(findInComment("mpcal", mpcalBlock))(
        buildReader(charSeq, underlying),
      ),
    )
    result.visit(Visitable.BottomUpFirstStrategy) { case loc: SourceLocatable =>
      assert(
        loc.sourceLocation.isInstanceOf[SourceLocationWithUnderlying],
        s"internal error: did not have source location: $loc",
      )
    }
    // ensure no dangling ref or [_] are left in random expressions
    result.visit(Visitable.BottomUpFirstStrategy) {
      case TLAExtensionExpression(pExp: MPCalRefExpr) =>
        assert(
          false,
          s"ref or [_] found in wrong expression context: these syntaxes may only be used directly as arguments to an MPCal procedure call: ${pExp.sourceLocation}",
        )
    }
    result
  }
}
