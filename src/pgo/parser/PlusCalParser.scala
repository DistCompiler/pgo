package pgo.parser

import pgo.model.mpcal.ModularPlusCalArchetype
import pgo.model.pcal._
import pgo.model.tla._
import pgo.util.SourceLocation

import scala.jdk.CollectionConverters._

final case class PCalParserContext(archetypes: Map[String,ModularPlusCalArchetype]=Map.empty)(implicit val ctx: TLAParserContext) {
  def withIdx(loc: SourceLocation, idx: Int, defn: TLADefinitionOne): PCalParserContext =
    copy()(ctx.copy(currentScope = ctx.currentScope.updated(new TLAIdentifier(loc, s"@$idx"), defn)))

  def withDefinition(defn: TLADefinition): PCalParserContext =
    copy()(ctx.withDefinition(defn))

  def withSelf(loc: SourceLocation, defn: TLADefinitionOne): PCalParserContext =
    copy()(ctx.withSelf(loc, defn))

  def withArchetype(arch: ModularPlusCalArchetype): PCalParserContext =
    copy(archetypes=archetypes.updated(arch.getName, arch))
}

object PCalParserContext {
  implicit def tlaCtx(implicit ctx: PCalParserContext): TLAParserContext = ctx.ctx
}

trait PlusCalParser extends TLAParser {
  import PCalParserContext.tlaCtx

  def findInComment[T](tag: =>Parser[Any], p: =>Parser[T]): Parser[T] = {
    val commentDelimiter: Parser[Any] = "(*" | "\\*" | "*)"
    val findComment: Parser[Any] = rep((not(commentDelimiter) ~> anything) | tlaLineComment) ^^^ ()
    val taggedComment: Parser[T] =
      "(*" ~> rep(tlaMultilineComment | tlaLineComment | (not(commentDelimiter | ("--" ~> tag)) ~> anything)) ~> guard("--" ~> tag) ~> commit(p) <~
        rep(tlaMultilineComment | tlaLineComment | (not(commentDelimiter) ~> anything)) <~ "*)"
    val emptyComment: Parser[Any] = "(*" ~> rep((not(commentDelimiter) ~> anything) | tlaLineComment | tlaMultilineComment) ~> "*)"

    lazy val search: Parser[T] =
      findComment ~> (taggedComment | (emptyComment ~> search))

    search <~ rep(anything)
  }

  override def tlaInfixOperator: Parser[String] =
    not("||" | ":=") ~> super.tlaInfixOperator

  val ws: Parser[Unit] = tlaWhitespace

  def pcalVarDecl(implicit ctx: PCalParserContext): Parser[PlusCalVariableDeclaration] = {
    val quantified =
      withSourceLocation {
        tlaIdentifierExpr ~ (ws ~> ("\\in" ^^^ true | "=" ^^^ false)) ~ (ws ~> tlaExpression)
      } ^^ {
        case (loc, id ~ isSet ~ v) =>
          new PlusCalVariableDeclaration(loc, id, false, isSet, v)
      }
    val id = tlaIdentifierExpr ^^ { id =>
      new PlusCalVariableDeclaration(id.getLocation, id, false, false, new PlusCalDefaultInitValue(id.getLocation))
    }
    quantified | id
  }

  def pcalPVarDecl(implicit ctx: PCalParserContext): Parser[PlusCalVariableDeclaration] = {
    val quantified =
      withSourceLocation {
        tlaIdentifierExpr ~ (ws ~> "=" ~> ws ~> tlaExpression)
      } ^^ {
        case (loc, id ~ v) =>
          new PlusCalVariableDeclaration(loc, id, false, false, v)
      }
    val id = tlaIdentifierExpr ^^ { id =>
      new PlusCalVariableDeclaration(id.getLocation, id, false, false, new PlusCalDefaultInitValue(id.getLocation))
    }
    quantified | id
  }

  def pcalVarDecls(implicit ctx: PCalParserContext): Parser[List[PlusCalVariableDeclaration]] =
    ("variables" | "variable") ~> ws ~> {
      def rec(implicit ctx: PCalParserContext): Parser[List[PlusCalVariableDeclaration]] = {
        val origCtx = ctx
        (ws ~> pcalVarDecl <~ ws <~ (";" | ",")).flatMap { decl =>
          implicit val ctx = origCtx.withDefinition(decl)
          rec ^^ (decl :: _) | success(List(decl))
        }
      }
      rec | success(Nil)
    }

  def pcalLhsId(implicit ctx: PCalParserContext): Parser[TLAExpression] =
    tlaIdentifierExpr <~ guard(ws ~> (":=" | "[" | ".")) ^^ { id => // avoid accidentally matching labels
      ctx.ctx.lookupDefinition(List(id)) match {
        case Some(defn) =>
          val result = new TLAGeneralIdentifier(id.getLocation, id, Nil)
          result.setRefersTo(defn)
          result
        case None =>
          throw DefinitionLookupError(id.getLocation, Nil, id)
      }
    }
  def pcalLhs(implicit ctx: PCalParserContext): Parser[TLAExpression] =
    withSourceLocation(pcalLhsId ~ (ws ~> "[" ~> ws ~> rep1sep(tlaExpression, ws ~> "," ~> ws) <~ ws <~ "]")) ^^ {
      case (loc, id ~ args) => new TLAFunctionCall(loc, id, args.asJava)
    } |
      withSourceLocation(pcalLhsId ~ (ws ~> "." ~> ws ~> tlaIdentifier)) ^^ {
        case (loc, id1 ~ id2) => new TLADot(loc, id1, id2)
      } | pcalLhsId

  def pcalAssignment(implicit ctx: PCalParserContext): Parser[PlusCalAssignment] = {
    val pairs = rep1sep(withSourceLocation(pcalLhs ~ (ws ~> ":=" ~> ws ~> tlaExpression)) ^^ {
      case (loc, lhs ~ rhs) => new PlusCalAssignmentPair(loc, lhs, rhs)
    }, ws ~> "||" ~> ws)
    withSourceLocation(pairs) ^^ { case (loc, pairs) => new PlusCalAssignment(loc, pairs.asJava) }
  }

  def pcalAwait(implicit ctx: PCalParserContext): Parser[PlusCalAwait] =
    withSourceLocation {
      ("await" | "when") ~> ws ~> tlaExpression
    } ^^ { case (loc, cond) => new PlusCalAwait(loc, cond) }

  def pcalPrint(implicit ctx: PCalParserContext): Parser[PlusCalPrint] =
    withSourceLocation {
      "print" ~> ws ~> tlaExpression
    } ^^ { case (loc, expr) => new PlusCalPrint(loc, expr) }

  def pcalAssert(implicit ctx: PCalParserContext): Parser[PlusCalAssert] =
    withSourceLocation {
      "assert" ~> ws ~> tlaExpression
    } ^^ { case (loc, cond) => new PlusCalAssert(loc, cond) }

  def pcalSkip(implicit ctx: PCalParserContext): Parser[PlusCalSkip] =
    withSourceLocation("skip") ^^ { case (loc, _) => new PlusCalSkip(loc) }

  def pcalReturn(implicit ctx: PCalParserContext): Parser[PlusCalReturn] =
    withSourceLocation("return") ^^ { case (loc, _) => new PlusCalReturn(loc) }

  def pcalGoto(implicit ctx: PCalParserContext): Parser[PlusCalGoto] =
    withSourceLocation("goto" ~> ws ~> tlaIdentifier) ^^ {
      case (loc, label) => new PlusCalGoto(loc, label)
    }

  def pcalCallParam(implicit ctx: PCalParserContext): Parser[TLAExpression] = tlaExpression
  def pcalCall(implicit ctx: PCalParserContext): Parser[PlusCalCall] =
    withSourceLocation {
      "call" ~> ws ~> tlaIdentifier ~ (ws ~> "(" ~> ws ~> repsep(pcalCallParam, ws ~> "," ~> ws) <~ ws <~ ")")
    } ^^ {
      case (loc, id ~ args) => new PlusCalCall(loc, id, args.asJava)
    }

  def pcalMacroCall(implicit ctx: PCalParserContext): Parser[PlusCalMacroCall] =
    withSourceLocation {
      tlaIdentifier ~ (ws ~> "(" ~> ws ~> repsep(tlaExpression, ws ~> "," ~> ws) <~ ws <~ ")")
    } ^^ { case (loc, id ~ args) => new PlusCalMacroCall(loc, id, args.asJava) }

  trait GenericSyntax {
    def pcalIf(implicit ctx: PCalParserContext): Parser[PlusCalIf]
    def pcalWhile(implicit ctx: PCalParserContext): Parser[PlusCalWhile]
    def pcalEither(implicit ctx: PCalParserContext): Parser[PlusCalEither]
    def pcalWith(implicit ctx: PCalParserContext): Parser[PlusCalWith]

    def pcalUnlabeledStmt(implicit ctx: PCalParserContext): Parser[PlusCalStatement] =
      pcalIf | pcalWhile | pcalEither | pcalWith | pcalAwait |
        pcalPrint | pcalAssert | pcalSkip | pcalReturn | pcalGoto | pcalCall |
        pcalMacroCall | pcalAssignment

    def pcalStmts(implicit ctx: PCalParserContext): Parser[List[PlusCalStatement]]

    def pcalBody(pSuffix: String)(implicit ctx: PCalParserContext): Parser[List[PlusCalStatement]]

    def pcalDefinitions(implicit ctx: PCalParserContext): Parser[List[TLAUnit]] = {
      "define" ~> ws ~> "{" ~> {
        def rec(implicit ctx: PCalParserContext): Parser[List[TLAUnit]] = {
          val origCtx = ctx
          (ws ~> tlaUnit).flatMap { unit =>
            implicit val ctx = unit.definitions.foldLeft(origCtx)(_.withDefinition(_))
            rec ^^ (unit :: _) | success(List(unit))
          }
        }
        rec | success(Nil)
      } <~ ws <~ "}" <~ opt(ws ~> ";")
    }

    def pcalMacro(implicit ctx: PCalParserContext): Parser[PlusCalMacro] =
      withSourceLocation {
        val origCtx = ctx
        "macro" ~> ws ~> tlaIdentifier ~ (ws ~> "(" ~> ws ~> repsep(tlaIdentifierExpr, ws ~> "," ~> ws)).flatMap { args =>
          implicit val ctx = args.foldLeft(origCtx)(_.withDefinition(_))
          (ws ~> ")" ~> ws ~> pcalBody("macro") <~ opt(ws ~> ";")) ^^ ((args, _))
        }
      } ^^ {
        case (loc, id ~ ((args, body))) => new PlusCalMacro(loc, id, args.asJava, body.asJava)
      }

    def pcalProcedureParam(implicit ctx: PCalParserContext): Parser[PlusCalVariableDeclaration] = pcalPVarDecl
    def pcalProcedure(implicit ctx: PCalParserContext): Parser[PlusCalProcedure] =
      withSourceLocation {
        val origCtx = ctx
        ("procedure" ~> ws ~> tlaIdentifier ~ (ws ~> "(" ~> ws ~> repsep(pcalProcedureParam, ws ~> "," ~> ws)) ~
          (ws ~> ")" ~> opt(ws ~> ("variables" | "variable") ~> ws ~> rep1sep(pcalPVarDecl, ws ~> (";"|",") ~> ws) <~ opt(ws ~> (";" | ","))))).flatMap {
          case id ~ args ~ locals =>
            implicit val ctx = locals.getOrElse(Nil).foldLeft(args.foldLeft(origCtx)(_.withDefinition(_)))(_.withDefinition(_))
            (ws ~> pcalBody("procedure") <~ opt(ws ~> ";")) ^^ ((id, args, locals, _))
        }
      } ^^ {
        case (loc, (id, args, locals, body)) =>
          new PlusCalProcedure(loc, id, args.asJava, locals.getOrElse(Nil).asJava, body.asJava)
      }

    def pcalProcessSelf(implicit ctx: PCalParserContext): Parser[PlusCalVariableDeclaration]
    def pcalProcess(implicit ctx: PCalParserContext): Parser[PlusCalProcess] =
      withSourceLocation {
        val origCtx = ctx
        ((("fair" ~> ws ~> "+" ^^^ PlusCalFairness.STRONG_FAIR) | ("fair" ^^^ PlusCalFairness.WEAK_FAIR) | success(PlusCalFairness.UNFAIR)) ~
          (ws ~> "process" ~> ws ~> pcalProcessSelf) ~ opt(ws ~> pcalVarDecls)).flatMap {
          case fairness ~ self ~ localsOpt =>
            implicit val ctx = localsOpt.getOrElse(Nil).foldLeft(origCtx.withSelf(self.getLocation, self))(_.withDefinition(_))
            (ws ~> pcalBody("process") <~ opt(ws ~> ";")) ^^ ((fairness, self, localsOpt.getOrElse(Nil), _))
        }
      } ^^ {
        case (loc, (fairness, self, locals, body)) =>
          new PlusCalProcess(loc, self, fairness, locals.asJava, body.asJava)
      }

    def pcalAlgorithmOpenBrace(implicit ctx: PCalParserContext): Parser[Unit]
    def pcalAlgorithmCloseBrace(implicit ctx: PCalParserContext): Parser[Unit]
    def pcalAlgorithm(implicit ctx: PCalParserContext): Parser[PlusCalAlgorithm] =
      withSourceLocation {
        val origCtx = ctx
        (("--algorithm" ^^^ PlusCalFairness.UNFAIR | "--fair algorithm" ^^^ PlusCalFairness.WEAK_FAIR) ~
          (ws ~> tlaIdentifierExpr) ~ (pcalAlgorithmOpenBrace ~> opt(ws ~> pcalVarDecls))).flatMap {
          case fairness ~ name ~ declsOpt =>
            implicit val ctx = declsOpt.getOrElse(Nil).foldLeft(origCtx)(_.withDefinition(_))
            val origCtx2 = ctx
            opt(ws ~> pcalDefinitions).flatMap { defnsOpt =>
              implicit val ctx = defnsOpt.getOrElse(Nil).foldLeft(origCtx2) { (ctx, unit) =>
                unit.definitions.foldLeft(ctx)(_.withDefinition(_))
              }
              (ws ~> repsep(pcalMacro, ws)) ~ (ws ~> repsep(pcalProcedure, ws)) ~ (ws ~> {
                withSourceLocation(pcalBody("algorithm")) ^^ { case (loc, stmts) => new PlusCalSingleProcess(loc, stmts.asJava) } |
                  withSourceLocation(rep1sep(pcalProcess, ws)) ^^ { case (loc, procs) => new PlusCalMultiProcess(loc, procs.asJava) }
              }) ^^ ((fairness, name, declsOpt, defnsOpt, _))
            }
        } <~ pcalAlgorithmCloseBrace
      } ^^ {
        case (loc, (fairness, name, declsOpt, defnsOpt, macros ~ procedures ~ proc)) =>
          new PlusCalAlgorithm(loc, fairness, name, declsOpt.getOrElse(Nil).asJava, macros.asJava, procedures.asJava, defnsOpt.getOrElse(Nil).asJava, proc)
      }
  }

  // make C-syntax overridable
  val pcalCSyntax: PCalCSyntax = new PCalCSyntax {}
  trait PCalCSyntax extends GenericSyntax {
    override def pcalIf(implicit ctx: PCalParserContext): Parser[PlusCalIf] =
      withSourceLocation {
        "if" ~> ws ~> "(" ~> tlaExpression ~ (ws ~> ")" ~> ws ~> pcalStmts) ~
          opt(opt(ws ~> ";") ~> ws ~> "else" ~> ws ~> pcalStmts)
      } ^^ {
        case (loc, cond ~ yes ~ noOpt) => new PlusCalIf(loc, cond, yes.asJava, noOpt.getOrElse(Nil).asJava)
      }

    override def pcalWhile(implicit ctx: PCalParserContext): Parser[PlusCalWhile] =
      withSourceLocation {
        "while" ~> ws ~> "(" ~> ws ~> tlaExpression ~ (ws ~> ")" ~> ws ~> pcalStmts)
      } ^^ {
        case (loc, cond ~ body) => new PlusCalWhile(loc, cond, body.asJava)
      }

    override def pcalEither(implicit ctx: PCalParserContext): Parser[PlusCalEither] =
      withSourceLocation {
        "either" ~> ws ~> pcalStmts ~ (ws ~> rep1sep("or" ~> ws ~> pcalStmts, ws))
      } ^^ {
        case (loc, part1 ~ parts) =>
          val convParts = part1.asJava :: parts.map(_.asJava)
          new PlusCalEither(loc, convParts.asJava)
      }

    override def pcalWith(implicit ctx: PCalParserContext): Parser[PlusCalWith] =
      withSourceLocation {
        "with" ~> ws ~> "(" ~> {
          def rec(rest: Boolean)(implicit ctx: PCalParserContext): Parser[(List[PlusCalVariableDeclaration],List[PlusCalStatement])] = {
            val origCtx = ctx
            (if(rest) {
              ws ~> (";" | ",")
            } else {
              ws
            }) ~> pcalVarDecl.flatMap { decl =>
              implicit val ctx = origCtx.withDefinition(decl)
              rec(true) ^^ (p => (decl :: p._1, p._2)) | (ws ~> ")" ~> ws ~> pcalStmts) ^^ ((List(decl), _))
            }
          }
          rec(false)
        }
      } ^^ {
        case (loc, (decls, body)) => new PlusCalWith(loc, decls.asJava, body.asJava)
      }

    def pcalCompoundStmt(implicit ctx: PCalParserContext): Parser[List[PlusCalStatement]] =
      "{" ~> ws ~> rep1sep(pcalStmts, ws ~> ";" ~> ws) <~ opt(ws ~> ";") <~ ws <~ "}" ^^ (_.flatten)

    def pcalLabeledStmt(implicit ctx: PCalParserContext): Parser[PlusCalLabeledStatements] =
      withSourceLocation {
        withSourceLocation {
          tlaIdentifier ~ (ws ~> ":" ~> ws ~> ("+" ^^^ PlusCalLabel.Modifier.PLUS | "-" ^^^ PlusCalLabel.Modifier.MINUS | success(PlusCalLabel.Modifier.NONE)))
        } ~! (ws ~> (rep1sep(pcalUnlabeledStmt, ws ~> ";" ~> ws) | pcalCompoundStmt))
      } ^^ {
        case (loc, (labelLoc, label ~ modifier) ~ body) =>
          new PlusCalLabeledStatements(loc, new PlusCalLabel(labelLoc, label, modifier), body.asJava)
      }

    override def pcalStmts(implicit ctx: PCalParserContext): Parser[List[PlusCalStatement]] =
      pcalUnlabeledStmt.map(List(_)) | pcalLabeledStmt.map(List(_)) | pcalCompoundStmt

    override def pcalBody(pSuffix: String)(implicit ctx: PCalParserContext): Parser[List[PlusCalStatement]] =
      pcalCompoundStmt

    override def pcalProcessSelf(implicit ctx: PCalParserContext): Parser[PlusCalVariableDeclaration] =
      "(" ~> ws ~> pcalVarDecl <~ ws <~ ")"

    override def pcalAlgorithmOpenBrace(implicit ctx: PCalParserContext): Parser[Unit] =
      ws ~> "{" ^^^ ()

    override def pcalAlgorithmCloseBrace(implicit ctx: PCalParserContext): Parser[Unit] =
      ws ~> "}" ^^^ ()
  }

  val pcalPSyntax: PCalPSyntax = new PCalPSyntax {}
  trait PCalPSyntax extends GenericSyntax {
    override def pcalIf(implicit ctx: PCalParserContext): Parser[PlusCalIf] = {
      lazy val elsePart: Parser[List[PlusCalStatement]] = {
        val elsif = withSourceLocation {
          "elsif" ~> ws ~> tlaExpression ~ (ws ~> "then" ~> ws ~> rep1sep(pcalStmt, ws)) ~ (ws ~> elsePart)
        } ^^ {
          case (loc, cond ~ yes ~ no) => List(new PlusCalIf(loc, cond, yes.asJava, no.asJava))
        }
        val els = "else" ~> ws ~> rep1sep(pcalStmt, ws)

        elsif | els | success(Nil)
      }

      withSourceLocation {
        "if" ~> ws ~> tlaExpression ~ (ws ~> "then" ~> ws ~> rep1sep(pcalStmt, ws) <~ ws) ~ elsePart <~ ws <~ "end" <~ ws <~ "if"
      } ^^ {
        case (loc, cond ~ yes ~ no) => new PlusCalIf(loc, cond, yes.asJava, no.asJava)
      }
    }

    override def pcalWhile(implicit ctx: PCalParserContext): Parser[PlusCalWhile] =
      withSourceLocation {
        "while" ~> ws ~> tlaExpression ~ (ws ~> "do" ~> ws  ~> rep1sep(pcalStmt, ws) <~ ws <~ "end" <~ ws <~ "while")
      } ^^ {
        case (loc, cond ~ body) => new PlusCalWhile(loc, cond, body.asJava)
      }

    override def pcalEither(implicit ctx: PCalParserContext): Parser[PlusCalEither] =
      withSourceLocation {
        "either" ~> ws ~> rep1sep(rep1sep(pcalStmt, ws), ws ~> "or" ~> ws) <~ ws <~ "end" <~ ws <~ "either"
      } ^^ {
        case (loc, parts) => new PlusCalEither(loc, parts.map(_.asJava).asJava)
      }

    override def pcalWith(implicit ctx: PCalParserContext): Parser[PlusCalWith] =
      withSourceLocation {
        "with" ~> {
          def rec(rest: Boolean)(implicit ctx: PCalParserContext): Parser[(List[PlusCalVariableDeclaration], List[PlusCalStatement])] = {
            val origCtx = ctx
            (if (rest) {
              ws ~> (";" | ",") ~> ws
            } else {
              ws
            }) ~> pcalVarDecl.flatMap { decl =>
              implicit val ctx = origCtx.withDefinition(decl)
              rec(true) ^^ (p => (decl :: p._1, p._2)) |
                (opt(ws ~> (";" | ",")) ~> ws ~> "do" ~> ws ~> rep1sep(pcalStmt, ws) <~ ws <~ "end" <~ ws <~ "with") ^^ ((List(decl), _))
            }
          }
          rec(false)
        }
      } ^^ {
        case (loc, (decls, body)) => new PlusCalWith(loc, decls.asJava, body.asJava)
      }

    def pcalStmt(implicit ctx: PCalParserContext): Parser[PlusCalStatement] = {
      val labeledStmts: Parser[PlusCalLabeledStatements] =
        withSourceLocation {
          withSourceLocation {
            tlaIdentifier ~ (ws ~> ":" ~> ws ~> ("+" ^^^ PlusCalLabel.Modifier.PLUS | "-" ^^^ PlusCalLabel.Modifier.MINUS | success(PlusCalLabel.Modifier.NONE)))
          } ~! (ws ~> rep1sep(pcalUnlabeledStmt, ws ~> ";" ~> ws) <~ ws <~ ";")
        } ^^ {
          case (loc, (labelLoc, label ~ mod) ~ stmts) =>
            new PlusCalLabeledStatements(loc, new PlusCalLabel(labelLoc, label, mod), stmts.asJava)
        }

      (pcalUnlabeledStmt <~ ws <~ ";") | labeledStmts
    }

    override def pcalStmts(implicit ctx: PCalParserContext): Parser[List[PlusCalStatement]] = rep1sep(pcalStmt, ws)

    override def pcalBody(pSuffix: String)(implicit ctx: PCalParserContext): Parser[List[PlusCalStatement]] =
      "begin" ~> ws ~> pcalStmts <~ ws <~ "end" <~ ws <~ pSuffix

    override def pcalProcessSelf(implicit ctx: PCalParserContext): Parser[PlusCalVariableDeclaration] = pcalVarDecl

    override def pcalAlgorithmOpenBrace(implicit ctx: PCalParserContext): Parser[Unit] = not(ws ~> "{")

    override def pcalAlgorithmCloseBrace(implicit ctx: PCalParserContext): Parser[Unit] = success(())
  }

  def pcalAlgorithm(implicit ctx: PCalParserContext): Parser[PlusCalAlgorithm] =
    pcalPSyntax.pcalAlgorithm | pcalCSyntax.pcalAlgorithm
}

object PlusCalParser extends PlusCalParser with ParsingUtils {
  def readAlgorithm(path: java.nio.file.Path, contents: CharSequence, tlaModule: TLAModule): PlusCalAlgorithm = {
    implicit val tlaCtx = TLAUtils.fillContextFromModule(
      TLABuiltinModules.Intrinsics.members.foldLeft(TLAParserContext())(_.withDefinition(_)),
      tlaModule, captureLocal = true)
    implicit val ctx = PCalParserContext()
    checkResult(phrase(findInComment("fair" | "algorithm", pcalAlgorithm))(buildReader(path, contents)))
  }
}
