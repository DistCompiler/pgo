package pgo.parser

import scala.collection.mutable
import pgo.model.{Definition, SourceLocatable, SourceLocation, SourceLocationWithUnderlying, Visitable}
import pgo.model.mpcal._
import pgo.model.pcal._
import pgo.model.tla._

import pgo.util.Description
import Description._

trait MPCalParser extends PCalParser {
  import pgo.parser.MPCalParserContext._
  import pgo.parser.PCalParserContext._

  private def cast[T](p: MPCalParser#Parser[T]): Parser[T] = p.asInstanceOf[Parser[T]]

  def mpcalRefSuffix: Parser[Int] =
    "^" ^^^ -1 | repsep("[" ~> ws ~> "_" ~> ws ~> "]", ws).map(_.length)

  def mpcalParam(implicit ctx: MPCalParserContext): Parser[MPCalParam] =
    withSourceLocation {
      "ref" ~> ws ~> tlaIdentifierExpr ~ (ws ~> mpcalRefSuffix) ^^ { case id ~ mappingCount => MPCalRefParam(id, mappingCount)} |
        (tlaIdentifierExpr <~ ws) ~ mpcalRefSuffix ^^ { case id ~ mappingCount => MPCalValParam(id, mappingCount) }
    }

  def mpcalArchetype(implicit ctx: MPCalParserContext): Parser[MPCalArchetype] =
    withSourceLocation {
      val origCtx = ctx
      ("archetype" ~> ws ~> tlaIdentifierExpr ~ (ws ~> "(" ~> ws ~> repsep(mpcalParam, ws ~> "," ~> ws) <~ ws <~ ")")).flatMap {
        case name ~ params =>
        val self = TLAIdentifier("self").setSourceLocation(name.sourceLocation).toDefiningIdentifier
          implicit val ctx: MPCalParserContext = params.foldLeft(origCtx.withDefinition(self))(_.withDefinition(_))
          val origCtx2 = ctx
          opt(ws ~> pcalVarDecls).flatMap { declsOpt =>
            implicit val ctx: MPCalParserContext = declsOpt.getOrElse(Nil).foldLeft(origCtx2)(_.withDefinition(_))
            (ws ~> pcalCSyntax.pcalCompoundStmt) ^^ ((name, self, params, declsOpt.getOrElse(Nil), _))
          }
      } ^^ {
        case (name, self, params, decls, body) => MPCalArchetype(name, self, params, decls, body)
      }
    }

  val mpcalMappingPosition: Parser[Int] =
    regex("""[1-9]\d*""".r).map(_.toInt)
  def mpcalMapping(positionMappings: Map[String,Int], maxPosition: Int)(implicit ctx: MPCalParserContext): Parser[MPCalMapping] =
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
            querySourceLocation("@" ~> mpcalMappingPosition) ~ (ws ~> mpcalRefSuffix) ^^ {
              case (positionLoc, position) ~ mappingCount =>
                if(position > maxPosition || position <= 0) {
                  throw MappingIndexOutOfBounds(positionLoc, position, maxPosition)
                }
                MPCalMappingTarget(position-1, mappingCount)
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

  def mpcalInstance(implicit ctx: MPCalParserContext): Parser[MPCalInstance] =
    withSourceLocation {
      ((("fair" ~> ws ~> "+" ^^^ PCalFairness.StrongFair) | ("fair" ^^^ PCalFairness.WeakFair) | success(PCalFairness.Unfair)) ~
        (ws ~> "process" ~> ws ~> "(" ~> pcalVarDeclBound <~ ws <~ ")") ~
        (ws ~> "==" ~> ws ~> "instance" ~> ws ~> tlaIdentifierExpr) ~
        (ws ~> "(" ~> ws ~> repsep(mpcalParam ^^ (Left(_)) | tlaExpression ^^ (Right(_)), ws ~> "," ~> ws) <~ ws <~ ")")).flatMap {
        case fairness ~ nameDecl ~ target ~ arguments =>
          val namePosMapping = arguments.view.zipWithIndex.collect {
            case (Left(param), idx) => param.name.id -> idx
          }.toMap
          ws ~> repsep(mpcalMapping(namePosMapping, arguments.size), ws) <~ ws <~ ";" ^^ { mappings =>
            ctx.archetypes.get(target) match {
              case None => throw ArchetypeLookupError(target)
              case Some(archetype) =>
                val result = MPCalInstance(nameDecl, fairness, target, arguments, mappings)
                result.setRefersTo(archetype)
                result
            }
          }
      }
    }

  def mpcalYield(implicit ctx: PCalParserContext): Parser[PCalExtensionStatement] =
    withSourceLocation {
      withSourceLocation {
        "yield" ~> ws ~>! tlaExpression ^^ MPCalYield
      } ^^ PCalExtensionStatement
    }

  object mpcalMappingMacroBody extends MPCalParser {
    def mpcalSpecialVariable(implicit ctx: TLAParserContext): Parser[TLAExpression] =
      withSourceLocation {
        withSourceLocation {
          "$variable" ^^ (_ => MPCalDollarVariable()) |
            "$value" ^^ (_ => MPCalDollarValue())
        } ^^ TLAExtensionExpression
      }

    override def tlaExpressionNoOperators(implicit ctx: TLAParserContext): Parser[TLAExpression] =
      mpcalSpecialVariable | super.tlaExpressionNoOperators

    override def pcalLhsId(implicit ctx: PCalParserContext): Parser[PCalAssignmentLhs] =
      withSourceLocation(mpcalSpecialVariable ^^ PCalAssignmentLhsExtension) | super.pcalLhsId

    override val pcalCSyntax: PCalCSyntax = new PCalCSyntax {
      override def pcalUnlabeledStmt(implicit ctx: PCalParserContext): Parser[PCalStatement] =
        mpcalYield | super.pcalUnlabeledStmt
    }
  }

  def mpcalMappingMacro(implicit ctx: MPCalParserContext): Parser[MPCalMappingMacro] =
    withSourceLocation {
      val origCtx = ctx
      ("mapping" ~> ws ~> "macro" ~> ws ~> tlaIdentifierExpr).flatMap { name =>
        implicit val ctx: MPCalParserContext = origCtx.withLateBinding
        (ws ~> "{" ~> ws ~> "read" ~> ws ~> cast(mpcalMappingMacroBody.pcalCSyntax.pcalCompoundStmt)) ~
          (ws ~> "write" ~> ws ~> cast(mpcalMappingMacroBody.pcalCSyntax.pcalCompoundStmt) <~ ws <~ "}") ^^
          ((name, _, ctx.ctx.ctx.lateBindingStack.head))
      } ^^ {
        case (name, readBlock ~ writeBlock, lateBindings) =>
          val freeVars = lateBindings.keysIterator.map(_.toDefiningIdentifier).toList.sortBy(_.id.id)
          freeVars.foreach { v => lateBindings(v.id).foreach(_(v)) }
          MPCalMappingMacro(name, readBlock, writeBlock, freeVars)
      }
    }

  def mpcalProcedure(implicit ctx: MPCalParserContext): Parser[MPCalProcedure] =
    withSourceLocation {
      val origCtx = ctx
      ("procedure" ~> ws ~> tlaIdentifierExpr).flatMap { id =>
        ((ws ~> "(" ~> ws ~> repsep(mpcalParam, ws ~> "," ~> ws)) ~
          (ws ~> ")" ~> opt(ws ~> ("variables" | "variable") ~> ws ~> rep1sep(pcalPVarDecl, ws ~> (";"|",") ~> ws) <~ opt(ws ~> (";" | ","))).map(_.getOrElse(Nil))))
          .flatMap {
            case args ~ locals =>
              implicit val ctx: MPCalParserContext = locals.foldLeft(args.foldLeft(origCtx)(_.withDefinition(_)))(_.withDefinition(_))
              (ws ~> cast(mpcalWithRefs.pcalCSyntax.pcalCompoundStmt) <~ opt(ws ~> ";")) ^^ ((id, args, locals, _))
          }
      } ^^ {
        case (id, args, locals, body) =>
          MPCalProcedure(id, args, locals, body)
      }
    }

  def mpcalWithRefs(implicit ctx: MPCalParserContext): MPCalParser =
    new MPCalParser {
      override def pcalCallParam(implicit ctx: PCalParserContext): Parser[TLAExpression] = {
        withSourceLocation {
          withSourceLocation {
            ("ref" ~> ws ~> tlaIdentifierExpr ~ (ws ~> mpcalRefSuffix) ^^ {
              case id ~ mappingCount => (id, MPCalRefExpr(id, mappingCount))
            } |
              tlaIdentifierExpr ~ (ws ~> mpcalRefSuffix) ^^ {
                case id ~ mappingCount => (id, MPCalValExpr(id, mappingCount))
              })
              .map {
                case (id, ref) =>
                  ctx.ctx.lookupDefinition(List(Definition.ScopeIdentifierName(id))) match {
                    case None =>
                      if(ctx.ctx.lateBindingStack.nonEmpty) {
                        ctx.ctx.lateBindingStack.head.getOrElseUpdate(id, mutable.ArrayBuffer()) += {
                          case param: MPCalParam => ref.setRefersTo(param)
                          case _ => throw KindMismatchError(ref.sourceLocation, d"expected procedure or archetype param reference")
                        }
                      } else {
                        throw DefinitionLookupError(Nil, Definition.ScopeIdentifierName(id))
                      }
                    case Some(defn) =>
                      defn match {
                        case param: MPCalParam => ref.setRefersTo(param)
                        case _ => throw KindMismatchError(ref.sourceLocation, d"expected procedure or archetype param reference")
                      }
                  }
                  ref
              }
          }.map(TLAExtensionExpression)
        } | super.pcalCallParam
      }
    }

  def mpcalBlock(implicit ctx: MPCalParserContext): Parser[MPCalBlock] =
    withSourceLocation {
      val origCtx = ctx
      (("--mpcal" ~> ws ~> tlaIdentifierExpr <~ ws <~ "{") ~ opt(ws ~> pcalDefinitions).map(_.getOrElse(Nil))).flatMap {
        case name ~ defns =>
          implicit val ctx: MPCalParserContext = defns.foldLeft(origCtx)((ctx, unit) => unit.definitions.foldLeft(ctx)(_.withDefinition(_)))
          val origCtx2 = ctx
          ((ws ~> repsep(cast(mpcalWithRefs.pcalCSyntax.pcalMacro), ws)) ~
            (ws ~> repsep(cast(mpcalWithRefs.mpcalProcedure), ws)) ~
            (ws ~> repsep(cast(mpcalWithRefs.mpcalMappingMacro), ws)) ~
            (ws ~> repsep(cast(mpcalWithRefs.mpcalArchetype), ws)) ~
            opt(ws ~> pcalVarDecls).map(_.getOrElse(Nil))).flatMap {
            case macros ~ mpcalProcedures ~ mappingMacros ~ archetypes ~ varDecls =>
              implicit val ctx: MPCalParserContext = {
                val tmp1 = archetypes.foldLeft(origCtx2)(_.withArchetype(_))
                val tmp2 = varDecls.foldLeft(tmp1)(_.withDefinition(_))
                mappingMacros.foldLeft(tmp2)(_.withMappingMacro(_))
              }
              (ws ~> repsep(mpcalInstance, ws)) ~
                (ws ~> repsep(cast(mpcalWithRefs.pcalCSyntax.pcalProcedure), ws)) ~ {
                (ws ~> cast(mpcalWithRefs.pcalCSyntax.pcalCompoundStmt)) ^^ (Left(_)) |
                  (ws ~> repsep(cast(mpcalWithRefs.pcalCSyntax.pcalProcess), ws)) ^^ (Right(_))
              } <~ ws <~ "}" ^^ ((name, defns, macros, mpcalProcedures, mappingMacros, archetypes, varDecls, _))
          }
      } ^^ {
        case (name, defns, macros, mpcalProcedures, mappingMacros, archetypes, varDecls, instances ~ pcalProcedures ~ procs) =>
          val dummyPCalProc = PCalProcedure(TLAIdentifier("dummy"), Nil, Nil, Nil) // a dummy PCal procedure to make auto-rename happy, see below
          var result = MPCalBlock(name, defns, macros, mpcalProcedures, mappingMacros, archetypes, varDecls, instances, dummyPCalProc :: pcalProcedures, procs)
          val macroMap = macros.view.map(m => m.name -> m).toMap
          result.visit() {
            case call @PCalMacroCall(target, _) =>
              macroMap.get(target) match {
                case Some(m) => call.setRefersTo(m)
                case None => throw MacroLookupError(target)
              }
          }
          val mpcalProcedureMap = mpcalProcedures.view.map(proc => proc.name -> proc).toMap
          val pcalProcedureMap = pcalProcedures.view.map((proc: PCalProcedure) => proc.name -> proc).toMap
          result.visit() {
            case call @PCalCall(target, _) =>
              pcalProcedureMap.get(target) match {
                case Some(procedure) => call.setRefersTo(procedure)
                case None if mpcalProcedureMap.contains(target) =>
                  // dummy value, whole AST node is replaced below
                  call.setRefersTo(dummyPCalProc)
                case None => throw ProcedureLookupError(target)
              }
          }
          // rewrite pcal proc calls to mpcal proc calls strictly at the end, to avoid messing up the auto-renaming in rewrite
          // like this, even if it's fake, all the parts have a refersTo, and the auto-renaming at least "thinks" it's working correctly
          result = result.rewrite() {
            case call @PCalCall(target, args) if mpcalProcedureMap.contains(target) =>
              PCalExtensionStatement(MPCalCall(target, args)
                .setSourceLocation(call.sourceLocation)
                .setRefersTo(mpcalProcedureMap(target))).setSourceLocation(call.sourceLocation)
          }
          // now the rewrite is done, drop the dummy PCal proc, which should have no more references
          val stableResult = result
          stableResult.decorateLike(stableResult.copy(pcalProcedures = result.pcalProcedures.tail).asInstanceOf[stableResult.type])
      }
    }
}

object MPCalParser extends MPCalParser with ParsingUtils {
  def hasMPCalBlock(underlying: SourceLocation.UnderlyingText, charSeq: CharSequence): Boolean =
    findInComment("mpcal", "--mpcal")(buildReader(charSeq, underlying)) match {
      case Success(_, _) => true
      case NoSuccess(_, _) => false
    }

  def readBlock(underlying: SourceLocation.UnderlyingText, charSeq: CharSequence, tlaModule: TLAModule): MPCalBlock = {
    implicit val tlaCtx: TLAParserContext =
      tlaModule.moduleDefinitions(captureLocal = true).foldLeft(
        BuiltinModules.Intrinsics.members.foldLeft(TLAParserContext())(_.withDefinition(_))
      )(_.withDefinition(_))
    implicit val pcalCtx: PCalParserContext = PCalParserContext()
    implicit val ctx: MPCalParserContext = MPCalParserContext()
    val result = checkResult(phrase(findInComment("mpcal", mpcalBlock))(buildReader(charSeq, underlying)))
    result.visit(Visitable.BottomUpFirstStrategy) {
      case loc: SourceLocatable => assert(loc.sourceLocation.isInstanceOf[SourceLocationWithUnderlying], s"internal error: did not have source location: $loc")
    }
    result
  }
}
