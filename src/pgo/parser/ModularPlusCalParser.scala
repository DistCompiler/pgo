package pgo.parser

import pgo.model.mpcal._
import pgo.model.pcal._
import pgo.model.tla._

import scala.jdk.CollectionConverters._

trait ModularPlusCalParser extends PlusCalParser {
  import pgo.parser.PCalParserContext.tlaCtx

  def mpcalVarDecl(implicit ctx: PCalParserContext): Parser[PlusCalVariableDeclaration] =
    withSourceLocation {
      opt("ref" ~> ws) ~ tlaIdentifierExpr
    } ^^ {
      case (loc, refOpt ~ id) =>
        new PlusCalVariableDeclaration(loc, id, refOpt.nonEmpty, false, new PlusCalDefaultInitValue(loc))
    }

  def mpcalParam(implicit ctx: PCalParserContext): Parser[TLAExpression] =
    withSourceLocation("ref" ~> ws ~> tlaIdentifierExpr) ^^ {
      case (loc, id) =>
        val result = new TLARef(loc, id.getId)
        ctx.ctx.lookupDefinition(List(id)) match {
          case None =>
            throw DefinitionLookupError(loc, Nil, id)
          case Some(defn) => result.setRefersTo(defn)
        }
        result
    } | tlaExpression

  def mpcalArchetype(implicit ctx: PCalParserContext): Parser[ModularPlusCalArchetype] =
    withSourceLocation {
      val origCtx = ctx
      ("archetype" ~> ws ~> tlaIdentifierExpr ~ (ws ~> "(" ~> ws ~> repsep(mpcalVarDecl, ws ~> "," ~> ws) <~ ws <~ ")")).flatMap {
        case name ~ args =>
          implicit val ctx = args.foldLeft(origCtx.withSelf(name.getLocation, name))(_.withDefinition(_))
          val origCtx2 = ctx
          opt(ws ~> pcalVarDecls).flatMap { declsOpt =>
            implicit val ctx = declsOpt.getOrElse(Nil).foldLeft(origCtx2)(_.withDefinition(_))
            (ws ~> pcalCSyntax.pcalCompoundStmt) ^^ ((name, args, declsOpt.getOrElse(Nil), _))
          }
      }
    } ^^ {
      case (loc, (name, args, decls, body)) =>
        new ModularPlusCalArchetype(loc, name, args.asJava, decls.asJava, body.asJava)
    }

  val mpcalMappingPosition: Parser[Int] =
    regex("""[1-9]\d*""".r).map(_.toInt)
  def mpcalMapping(implicit ctx: PCalParserContext): Parser[ModularPlusCalMapping] =
    withSourceLocation {
      "mapping" ~> ws ~> {
        withSourceLocation(tlaIdentifierExpr ~ opt(ws ~> "[_]")) ^^ {
          case (loc, id ~ paramOpt) =>
            val result = new ModularPlusCalMappingVariableName(loc, id, paramOpt.nonEmpty)
            ctx.ctx.lookupDefinition(List(id)) match {
              case None => throw DefinitionLookupError(loc, Nil, id)
              case Some(defn) => result.setRefersTo(defn)
            }
            result
        } |
          withSourceLocation("@" ~> mpcalMappingPosition ~ opt(ws ~> "[_]")) ^^ {
            case (loc, pos ~ paramOpt) => // note: we leave setRefersTo for DefinitionRegistry
              new ModularPlusCalMappingVariablePosition(loc, pos, paramOpt.nonEmpty)
          }
      } ~ (ws ~> "via" ~> ws ~> tlaIdentifierExpr)
    } ^^ {
      case (loc, vrble ~ via) =>
        new ModularPlusCalMapping(loc, vrble, new ModularPlusCalMappingTarget(via.getLocation, via.getId))
    }

  def mpcalInstance(implicit ctx: PCalParserContext): Parser[ModularPlusCalInstance] =
    withSourceLocation {
      (("fair" ~> ws ~> "+" ^^^ PlusCalFairness.STRONG_FAIR) | ("fair" ^^^ PlusCalFairness.WEAK_FAIR) | success(PlusCalFairness.UNFAIR)) ~
        (ws ~> "process" ~> ws ~> "(" ~> pcalVarDecl <~ ws <~ ")") ~
        (ws ~> "==" ~> ws ~> "instance" ~> ws ~> tlaIdentifierExpr) ~
        (ws ~> "(" ~> ws ~> repsep(mpcalParam, ws ~> "," ~> ws) <~ ws <~ ")") ~
        (ws ~> repsep(mpcalMapping, ws) <~ ws <~ ";")
    } ^^ {
      case (loc, fairness ~ nameDecl ~ target ~ params ~ mappings) =>
        ctx.archetypes.get(target.getId) match {
          case None => throw DefinitionLookupError(target.getLocation, Nil, target)
          case Some(arch) =>
            mappings.foreach { mapping =>
              mapping.getVariable match {
                case name: ModularPlusCalMappingVariableName =>
                case position: ModularPlusCalMappingVariablePosition if 0 < position.getPosition && position.getPosition <= arch.getParams.size() =>
                  // bizarre edge case: indexed mappings refer to _the archetype's parameter at the correct position_, not the expression they map over
                  // in the instance param list
                  position.setRefersTo(arch.getParams.asScala(position.getPosition - 1))
                case v =>
                  throw DefinitionLookupError(v.getLocation, Nil, new TLAIdentifier(v.getLocation, v.toString))
              }
            }
        }
        new ModularPlusCalInstance(loc, nameDecl, fairness, target, params.asJava, mappings.asJava)
    }

  def mpcalYield(implicit ctx: PCalParserContext): Parser[ModularPlusCalYield] =
    withSourceLocation {
      "yield" ~> ws ~>! tlaExpression
    } ^^ { case (loc, expr) => new ModularPlusCalYield(loc, expr) }

  object mpcalMappingMacroBody extends ModularPlusCalParser {
    def mpcalSpecialVariable(implicit ctx: TLAParserContext): Parser[TLAExpression] =
      withSourceLocation("$variable") ^^ { case (loc, _) => new TLASpecialVariableVariable(loc) } |
        withSourceLocation("$value") ^^ { case (loc, _) => new TLASpecialVariableValue(loc) }

    override def tlaExpressionNoOperators(implicit ctx: TLAParserContext): Parser[TLAExpression] =
      mpcalSpecialVariable | super.tlaExpressionNoOperators

    override def pcalLhsId(implicit ctx: PCalParserContext): Parser[TLAExpression] =
      mpcalSpecialVariable | super.pcalLhsId

    override val pcalCSyntax: PCalCSyntax = new PCalCSyntax {
      override def pcalUnlabeledStmt(implicit ctx: PCalParserContext): Parser[PlusCalStatement] =
        mpcalYield | super.pcalUnlabeledStmt
    }
  }

  implicit class mpcalMappingMacroBodyParserToParser[T](p: mpcalMappingMacroBody.Parser[T]) {
    def cast: Parser[T] = p.asInstanceOf[Parser[T]]
  }

  def mpcalMappingMacro(implicit ctx: PCalParserContext): Parser[ModularPlusCalMappingMacro] =
    withSourceLocation {
      val origCtx = ctx
      ("mapping" ~> ws ~> "macro" ~> ws ~> tlaIdentifierExpr).flatMap { name =>
        implicit val ctx = origCtx.withSelf(name.getLocation, name)
        (ws ~> "{" ~> ws ~> "read" ~> ws ~> mpcalMappingMacroBody.pcalCSyntax.pcalCompoundStmt.cast) ~
          (ws ~> "write" ~> ws ~> mpcalMappingMacroBody.pcalCSyntax.pcalCompoundStmt.cast <~ ws <~ "}") ^^
          ((name, _))
      }
    } ^^ {
      case (loc, (name, readBlock ~ writeBlock)) =>
        new ModularPlusCalMappingMacro(loc, name, readBlock.asJava, writeBlock.asJava)
    }

  object mpcalWithRefs extends ModularPlusCalParser {
    override def pcalCallParam(implicit ctx: PCalParserContext): Parser[TLAExpression] = mpcalParam

    override val pcalCSyntax: PCalCSyntax = new PCalCSyntax {
      override def pcalProcedureParam(implicit ctx: PCalParserContext): Parser[PlusCalVariableDeclaration] =
        mpcalVarDecl | super.pcalProcedureParam
    }
  }

  implicit class mpcalWithRefsToParser[T](p: mpcalWithRefs.Parser[T]) {
    def cast: Parser[T] = p.asInstanceOf[Parser[T]]
  }

  def mpcalBlock(implicit ctx: PCalParserContext): Parser[ModularPlusCalBlock] =
    withSourceLocation {
      val origCtx = ctx
      (("--mpcal" ~> ws ~> tlaIdentifierExpr <~ ws <~ "{") ~ opt(ws ~> pcalCSyntax.pcalDefinitions).map(_.getOrElse(Nil))).flatMap {
        case name ~ defns =>
          implicit val ctx = defns.foldLeft(origCtx)((ctx, unit) => unit.definitions.foldLeft(ctx)(_.withDefinition(_)))
          val origCtx2 = ctx
          (rep(ws ~> pcalCSyntax.pcalMacro) ~
            rep(ws ~> mpcalWithRefs.pcalCSyntax.pcalProcedure.cast) ~
            rep(ws ~> mpcalWithRefs.mpcalMappingMacro.cast) ~
            rep(ws ~> mpcalWithRefs.mpcalArchetype.cast) ~
            opt(ws ~> pcalVarDecls).map(_.getOrElse(Nil))).flatMap {
            case macros ~ procedures ~ mappingMacros ~ archetypes ~ varDecls =>
              implicit val ctx = {
                val tmp = archetypes.foldLeft(origCtx2)(_.withArchetype(_))
                varDecls.foldLeft(tmp)(_.withDefinition(_))
              }
              rep(ws ~> mpcalInstance) ~ {
                (ws ~> withSourceLocation(pcalCSyntax.pcalCompoundStmt)) ^^ { case (loc, stmts) => new PlusCalSingleProcess(loc, stmts.asJava) } |
                  (ws ~> withSourceLocation(repsep(pcalCSyntax.pcalProcess, ws))) ^^ { case (loc, procs) => new PlusCalMultiProcess(loc, procs.asJava) }
              } <~ ws <~ "}" ^^ ((name, defns, macros, procedures, mappingMacros, archetypes, varDecls, _))
          }
      }
    } ^^ {
      case (loc, (name, defns, macros, procedures, mappingMacros, archetypes, varDecls, instances ~ procs)) =>
        new ModularPlusCalBlock(loc, name, defns, macros, procedures, mappingMacros, archetypes, varDecls, instances, procs)
    }
}

object ModularPlusCalParser extends ModularPlusCalParser with ParsingUtils {
  def hasModularPlusCalBlock(path: java.nio.file.Path, charSeq: CharSequence): Boolean =
    findInComment("mpcal", "--mpcal")(buildReader(path, charSeq)) match {
      case Success(_, _) => true
      case NoSuccess(_, _) => false
    }

  def readBlock(path: java.nio.file.Path, charSeq: CharSequence, tlaModule: TLAModule): ModularPlusCalBlock = {
    implicit val tlaCtx = TLAUtils.fillContextFromModule(
      TLABuiltinModules.Intrinsics.members.foldLeft(TLAParserContext())(_.withDefinition(_)),
      tlaModule, captureLocal = true)
    implicit val ctx = PCalParserContext()
    checkResult(phrase(findInComment("mpcal", mpcalBlock))(buildReader(path, charSeq)))
  }
}
