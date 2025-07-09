package pgo.parser

import pgo.model.Definition.ScopeIdentifier
import pgo.model.{Definition, DefinitionOne, SourceLocation, Visitable}
import pgo.model.pcal._
import pgo.model.tla._
import pgo.parser.PCalParserContext.given

import scala.collection.mutable

trait PCalParser extends TLAParser {
  import PCalParserContext._

  def findInComment[T](tag: => Parser[Any], p: => Parser[T]): Parser[T] = {
    val commentDelimiter: Parser[Any] = "(*" | "\\*" | "*)"
    val findComment: Parser[Any] =
      rep((not(commentDelimiter) ~> anything) | tlaLineComment) ^^^ ()
    val taggedComment: Parser[T] =
      "(*" ~> rep(
        tlaMultilineComment | tlaLineComment | (not(
          commentDelimiter | ("--" ~> tag),
        ) ~> anything),
      ) ~> guard("--" ~> tag) ~> commit(p) <~
        rep(
          tlaMultilineComment | tlaLineComment | (not(
            commentDelimiter,
          ) ~> anything),
        ) <~ "*)"
    val emptyComment: Parser[Any] = "(*" ~> rep(
      (not(commentDelimiter) ~> anything) | tlaLineComment | tlaMultilineComment,
    ) ~> "*)"

    lazy val search: Parser[T] =
      findComment ~> (taggedComment | (emptyComment ~> search))

    search <~ rep(anything)
  }

  override def tlaInfixOperator: Parser[TLASymbol] =
    not("||" | ":=") ~> super.tlaInfixOperator

  val ws: Parser[Unit] = tlaWhitespace

  def pcalVarDeclBound(using
      ctx: PCalParserContext,
  ): Parser[PCalVariableDeclarationBound] =
    withSourceLocation {
      tlaIdentifierExpr ~ (ws ~> ("\\in" ^^^ true | "=" ^^^ false)) ~ (ws ~> tlaExpression) ^^ {
        case id ~ true ~ v =>
          PCalVariableDeclarationSet(id, v)
        case id ~ false ~ v =>
          PCalVariableDeclarationValue(id, v)
      }
    }

  def pcalVarDecl(using
      ctx: PCalParserContext,
  ): Parser[PCalVariableDeclaration] =
    pcalVarDeclBound | withSourceLocation {
      tlaIdentifierExpr ^^ PCalVariableDeclarationEmpty.apply
    }

  def pcalPVarDecl(using
      ctx: PCalParserContext,
  ): Parser[PCalPVariableDeclaration] =
    withSourceLocation {
      tlaIdentifierExpr ~ opt(ws ~> "=" ~> ws ~> tlaExpression) ^^ {
        case id ~ valueOpt => PCalPVariableDeclaration(id, valueOpt)
      }
    }

  def pcalVarDecls(using
      ctx: PCalParserContext,
  ): Parser[List[PCalVariableDeclaration]] =
    ("variables" | "variable") ~> ws ~> {
      def rec(using
          ctx: PCalParserContext,
      ): Parser[List[PCalVariableDeclaration]] = {
        val origCtx = ctx
        (ws ~> pcalVarDecl <~ ws <~ (";" | ",")).flatMap { decl =>
          given ctx: PCalParserContext = origCtx.withDefinition(decl)
          rec ^^ (decl :: _) | success(List(decl))
        }
      }
      rec | success(Nil)
    }

  def pcalLhsId(using ctx: PCalParserContext): Parser[PCalAssignmentLhs] = {
    val lhsPart: Parser[Any] =
      ("." ~> ws ~> tlaIdentifier) |
        ("[" ~> ws ~> rep1sep(tlaExpression, ws ~> "," ~> ws) <~ ws <~ "]")

    withSourceLocation {
      tlaIdentifierExpr <~ guard(ws ~> repsep(lhsPart, ws) ~> ws ~> ":=") ^^ {
        id => // avoid accidentally matching non-assignments
          ctx.ctx.lookupDefinition(
            List(Definition.ScopeIdentifierName(id)),
          ) match {
            case Some(defn) =>
              val result = PCalAssignmentLhsIdentifier(id)
              result.setRefersTo(defn)
              result
            case None if ctx.ctx.lateBindingStack > 0 =>
              // let whoever incremented lateBindingStack set the reference later
              // this should be the parser for PCalMacro
              PCalAssignmentLhsIdentifier(id)
            case None =>
              throw DefinitionLookupError(
                Nil,
                Definition.ScopeIdentifierName(id),
              )
          }
      }
    }
  }

  def pcalLhs(using ctx: PCalParserContext): Parser[PCalAssignmentLhs] = {
    def rec(lhs: PCalAssignmentLhs): Parser[PCalAssignmentLhs] =
      opt {
        ws ~> (querySourceLocation {
          "." ~> ws ~> tlaIdentifierExpr ^^ (id =>
            PCalAssignmentLhsProjection(
              lhs,
              List(TLAString(id.id).setSourceLocation(id.sourceLocation)),
            )
          ) |
            "[" ~> ws ~> rep1sep(
              tlaExpression,
              ws ~> "," ~> ws,
            ) <~ ws <~ "]" ^^ (PCalAssignmentLhsProjection(lhs, _))
        } ^^ { case (loc, proj) =>
          proj.setSourceLocation(
            lhs.sourceLocation ++ loc,
          ) // ensure the projection's position includes LHS
        })
          .flatMap(rec)
      }
        .map(_.getOrElse(lhs))

    pcalLhsId.flatMap(rec)
  }

  def pcalAssignment(using ctx: PCalParserContext): Parser[PCalAssignment] =
    withSourceLocation {
      rep1sep(
        withSourceLocation {
          pcalLhs ~ (ws ~> ":=" ~> ws ~> tlaExpression) ^^ { case lhs ~ rhs =>
            PCalAssignmentPair(lhs, rhs)
          }
        },
        ws ~> "||" ~> ws,
      ) ^^ PCalAssignment.apply
    }

  def pcalAwait(using ctx: PCalParserContext): Parser[PCalAwait] =
    withSourceLocation {
      ("await" | "when") ~> ws ~> tlaExpression ^^ PCalAwait.apply
    }

  def pcalPrint(using ctx: PCalParserContext): Parser[PCalPrint] =
    withSourceLocation {
      "print" ~> ws ~> tlaExpression ^^ PCalPrint.apply
    }

  def pcalAssert(using ctx: PCalParserContext): Parser[PCalAssert] =
    withSourceLocation {
      "assert" ~> ws ~> tlaExpression ^^ PCalAssert.apply
    }

  def pcalSkip(using ctx: PCalParserContext): Parser[PCalSkip] =
    withSourceLocation("skip" ^^ (_ => PCalSkip()))

  def pcalReturn(using ctx: PCalParserContext): Parser[PCalReturn] =
    withSourceLocation("return" ^^ (_ => PCalReturn()))

  def pcalGoto(using ctx: PCalParserContext): Parser[PCalGoto] =
    withSourceLocation {
      "goto" ~> ws ~> tlaIdentifier ^^ PCalGoto.apply
    }

  def pcalCallParam(using ctx: PCalParserContext): Parser[TLAExpression] =
    tlaExpression
  def pcalCall(using ctx: PCalParserContext): Parser[PCalCall] =
    withSourceLocation {
      "call" ~> ws ~> tlaIdentifierExpr ~ (ws ~> "(" ~> ws ~> repsep(
        pcalCallParam,
        ws ~> "," ~> ws,
      ) <~ ws <~ ")") ^^ { case id ~ args =>
        PCalCall(id, args) // has refersTo, but will be assigned later
      }
    }

  def pcalMacroCall(using ctx: PCalParserContext): Parser[PCalMacroCall] =
    withSourceLocation {
      tlaIdentifierExpr ~ (ws ~> "(" ~> ws ~> repsep(
        tlaExpression,
        ws ~> "," ~> ws,
      ) <~ ws <~ ")") ^^ { case id ~ args =>
        PCalMacroCall(
          id,
          args,
        ) // has refersTo, but will be assigned later when parsing algorithm
      }
    }

  def pcalDefinitions(using
      ctx: PCalParserContext,
  ): Parser[List[TLAUnit]] = {
    "define" ~> ws ~> "{" ~> {
      def rec(using ctx: PCalParserContext): Parser[List[TLAUnit]] = {
        val origCtx = ctx
        (ws ~> tlaUnit).flatMap { unit =>
          given ctx: PCalParserContext =
            unit.definitions.foldLeft(origCtx)(_.withDefinition(_))
          rec ^^ (unit :: _) | success(List(unit))
        }
      }
      rec | success(Nil)
    } <~ ws <~ "}" <~ opt(ws ~> ";")
  }

  trait GenericSyntax {
    def pcalIf(using ctx: PCalParserContext): Parser[PCalIf]
    def pcalWhile(using ctx: PCalParserContext): Parser[PCalWhile]
    def pcalEither(using ctx: PCalParserContext): Parser[PCalEither]
    def pcalWith(using ctx: PCalParserContext): Parser[PCalWith]

    def pcalUnlabeledStmt(using
        ctx: PCalParserContext,
    ): Parser[PCalStatement] =
      pcalIf | pcalWhile | pcalEither | pcalWith | pcalAwait |
        pcalPrint | pcalAssert | pcalSkip | pcalReturn | pcalGoto | pcalCall |
        pcalMacroCall | pcalAssignment

    def pcalStmts(using ctx: PCalParserContext): Parser[List[PCalStatement]]

    def pcalBody(pSuffix: String)(using
        ctx: PCalParserContext,
    ): Parser[List[PCalStatement]]

    def pcalMacro(using ctx: PCalParserContext): Parser[PCalMacro] =
      withSourceLocation {
        val origCtx = ctx
        "macro" ~> ws ~> tlaIdentifierExpr ~ (ws ~> "(" ~> ws ~> repsep(
          tlaIdentifierExpr,
          ws ~> "," ~> ws,
        )).flatMap { params =>
          val definingParams = params.map(_.toDefiningIdentifier)
          given ctx: PCalParserContext = definingParams
            .foldLeft(origCtx)(_.withDefinition(_))
            .withLateBinding
          (ws ~> ")" ~> ws ~> pcalBody("macro") <~ opt(ws ~> ";")) ^^ ((
            definingParams,
            _,
          ))
        } ^^ { case id ~ ((params, body)) =>
          val freeVars = locally {
            val freeVarsAcc = mutable.HashMap[TLAIdentifier, mutable.ListBuffer[
              DefinitionOne => Unit,
            ]]()
            body.foreach(_.visit(Visitable.TopDownFirstStrategy) {
              case ident @ TLAGeneralIdentifier(name, Nil)
                  if !ident.hasRefersTo =>
                freeVarsAcc.getOrElseUpdate(
                  name,
                  mutable.ListBuffer(),
                ) += ident.setRefersTo
              case lhs @ PCalAssignmentLhsIdentifier(name)
                  if !lhs.hasRefersTo =>
                freeVarsAcc.getOrElseUpdate(
                  name,
                  mutable.ListBuffer(),
                ) += lhs.setRefersTo
            })
            freeVarsAcc.toMap
          }
          val freeVarsList = freeVars.keysIterator.toArray
            .sortInPlaceBy(_.id)
            .iterator
            .map(_.toDefiningIdentifier)
            .toList
          freeVarsList.foreach { ident =>
            freeVars(ident.id).foreach(_(ident))
          }
          PCalMacro(id, params, body, freeVarsList)
        }
      }

    def pcalProcedure(using ctx: PCalParserContext): Parser[PCalProcedure] =
      withSourceLocation {
        val origCtx = ctx
        querySourceLocation("procedure" ~> ws ~> tlaIdentifierExpr).flatMap {
          case (selfLoc, id) =>
            val selfDecl = TLAIdentifier("self")
              .setSourceLocation(selfLoc)
              .toDefiningIdentifier
            given ctx: PCalParserContext =
              origCtx.withDefinition(selfDecl)
            val origCtx2 = ctx
            ((ws ~> "(" ~> ws ~> repsep(pcalPVarDecl, ws ~> "," ~> ws)) ~
              (ws ~> ")" ~> opt(
                ws ~> ("variables" | "variable") ~> ws ~> rep1sep(
                  pcalPVarDecl,
                  ws ~> (";" | ",") ~> ws,
                ) <~ opt(ws ~> (";" | ",")),
              ).map(_.getOrElse(Nil))))
              .flatMap { case args ~ locals =>
                given ctx: PCalParserContext = locals.foldLeft(
                  args.foldLeft(origCtx2)(_.withDefinition(_)),
                )(_.withDefinition(_))
                (ws ~> pcalBody("procedure") <~ opt(ws ~> ";")) ^^ ((
                  id,
                  selfDecl,
                  args,
                  locals,
                  _,
                ))
              }
        } ^^ { case (id, selfDecl, args, locals, body) =>
          PCalProcedure(id, selfDecl, args, locals, body)
        }
      }

    def pcalProcessSelf(using
        ctx: PCalParserContext,
    ): Parser[PCalVariableDeclarationBound]
    def pcalProcess(using ctx: PCalParserContext): Parser[PCalProcess] =
      withSourceLocation {
        val origCtx = ctx
        ((("fair" ~> ws ~> "+" ^^^ PCalFairness.StrongFair) | ("fair" ^^^ PCalFairness.WeakFair) | success(
          PCalFairness.Unfair,
        )) ~
          (ws ~> "process" ~> ws ~> pcalProcessSelf)).flatMap {
          case fairness ~ self =>
            given ctx: PCalParserContext = origCtx.withProcessSelf(self)
            val origCtx2 = ctx
            opt(ws ~> pcalVarDecls).map(_.getOrElse(Nil)).flatMap { locals =>
              given ctx: PCalParserContext =
                locals.foldLeft(origCtx2)(_.withDefinition(_))
              (ws ~> pcalBody("process") <~ opt(ws ~> ";")) ^^ ((
                fairness,
                self,
                locals,
                _,
              ))
            }
        } ^^ { case (fairness, self, locals, body) =>
          PCalProcess(self, fairness, locals, body)
        }
      }

    def pcalAlgorithmOpenBrace(using ctx: PCalParserContext): Parser[Unit]
    def pcalAlgorithmCloseBrace(using ctx: PCalParserContext): Parser[Unit]
    def pcalAlgorithm(using ctx: PCalParserContext): Parser[PCalAlgorithm] =
      withSourceLocation {
        val origCtx =
          ctx.withLateBinding // for bleed references between processes and procedures
        locally {
          given ctx: PCalParserContext =
            origCtx.withLateBinding // decls may reference definitions
          (("--algorithm" ^^^ PCalFairness.Unfair | "--fair algorithm" ^^^ PCalFairness.WeakFair) ~
            (ws ~> tlaIdentifierExpr) ~ (pcalAlgorithmOpenBrace ~> opt(
              ws ~> pcalVarDecls,
            ).map(_.getOrElse(Nil)))).flatMap { case fairness ~ name ~ decls =>
            given ctx: PCalParserContext =
              decls.foldLeft(origCtx)(_.withDefinition(_))
            val origCtx2 = ctx
            opt(ws ~> pcalDefinitions).map(_.getOrElse(Nil)).flatMap { defns =>
              val defnsSingleDefinitions = defns.view
                .flatMap(_.definitions.flatMap(_.singleDefinitions))
                .toList
              // because pcalDefinitions appear after pcalVarDecls, but may be references by the latter, we have to
              // allow for this with "late bindings"
              decls.foreach { decl =>
                origCtx.ctx
                  .resolveLateBindings(decl, defns = defnsSingleDefinitions)
              }
              given ctx: PCalParserContext =
                defnsSingleDefinitions.foldLeft(origCtx2)(_.withDefinition(_))
              (ws ~> repsep(pcalMacro, ws)) ~
                (ws ~> repsep(pcalProcedure, ws)) ~
                (ws ~> {
                  pcalBody("algorithm") ^^ (Left(_)) |
                    rep1sep(pcalProcess, ws) ^^ (Right(_))
                }) ^^ ((fairness, name, decls, defns, _))
            }
          }
        } <~ pcalAlgorithmCloseBrace ^^ {
          case (fairness, name, decls, defns, macros ~ procedures ~ proc) =>
            val result = PCalAlgorithm(
              fairness,
              name,
              decls,
              defns,
              macros,
              procedures,
              proc,
            )
            val macroMap = macros.view.map(m => m.name -> m).toMap
            result.visit() { case call @ PCalMacroCall(target, _) =>
              macroMap.get(target) match {
                case Some(mcro) => call.setRefersTo(mcro)
                case None       => throw MacroLookupError(target)
              }
            }
            val procedureMap =
              procedures.view.map(proc => proc.name -> proc).toMap
            result.visit() { case call @ PCalCall(target, _) =>
              procedureMap.get(target) match {
                case Some(procedure) => call.setRefersTo(procedure)
                case None            => throw ProcedureLookupError(target)
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
            ctx.ctx.resolveLateBindings(
              result,
              bleedableDefs.filter(defn =>
                !bleedableDefsWithDups(defn.identifier),
              ),
            )

            result
        }
      }
  }

  // make C-syntax overridable
  val pcalCSyntax: PCalCSyntax = new PCalCSyntax {}
  trait PCalCSyntax extends GenericSyntax {
    override def pcalIf(using ctx: PCalParserContext): Parser[PCalIf] =
      withSourceLocation {
        "if" ~>! ws ~> "(" ~> ws ~> tlaExpression ~ (ws ~> ")" ~> ws ~> pcalStmts) ~
          opt(opt(ws ~> ";") ~> ws ~> "else" ~> ws ~> pcalStmts)
            .map(_.getOrElse(Nil)) ^^ { case cond ~ yes ~ no =>
            PCalIf(cond, yes, no)
          }
      }

    override def pcalWhile(using ctx: PCalParserContext): Parser[PCalWhile] =
      withSourceLocation {
        "while" ~>! ws ~> "(" ~> ws ~> tlaExpression ~ (ws ~> ")" ~> ws ~> pcalStmts) ^^ {
          case cond ~ body => PCalWhile(cond, body)
        }
      }

    override def pcalEither(using
        ctx: PCalParserContext,
    ): Parser[PCalEither] =
      withSourceLocation {
        "either" ~>! ws ~> pcalStmts ~ (ws ~> rep1sep(
          "or" ~> ws ~> pcalStmts,
          ws,
        )) ^^ { case part1 ~ parts =>
          PCalEither(part1 :: parts)
        }
      }

    override def pcalWith(using ctx: PCalParserContext): Parser[PCalWith] =
      withSourceLocation {
        "with" ~>! ws ~> "(" ~> {
          def rec(rest: Boolean)(using
              ctx: PCalParserContext,
          ): Parser[
            (List[PCalVariableDeclarationBound], List[PCalStatement]),
          ] = {
            val origCtx = ctx
            (if (rest) {
               ws ~> (";" | ",") ~> ws
             } else {
               ws
             }) ~> pcalVarDeclBound.flatMap { decl =>
              given ctx: PCalParserContext = origCtx.withDefinition(decl)
              rec(true) ^^ (p =>
                (decl :: p._1, p._2)
              ) | (ws ~> ")" ~> ws ~> pcalStmts) ^^ ((List(decl), _))
            }
          }
          rec(false)
        } ^^ { case (decls, body) =>
          PCalWith(decls, body)
        }
      }

    def pcalCompoundStmt(using
        ctx: PCalParserContext,
    ): Parser[List[PCalStatement]] =
      "{" ~> ws ~> rep1sep(pcalStmts, ws ~> ";" ~> ws) <~ opt(
        ws ~> ";",
      ) <~ ws <~ "}" ^^ (_.flatten)

    def pcalLabeledStmt(using
        ctx: PCalParserContext,
    ): Parser[PCalLabeledStatements] =
      withSourceLocation {
        querySourceLocation {
          tlaIdentifier ~ (ws ~> not(
            ":=",
          ) ~> ":" ~> ws ~> ("+" ^^^ PCalLabel.PlusModifier | "-" ^^^ PCalLabel.MinusModifier | success(
            PCalLabel.NoModifier,
          )))
        } ~! (ws ~> (rep1sep(
          pcalUnlabeledStmt,
          ws ~> ";" ~> ws,
        ) | pcalCompoundStmt)) ^^ { case (labelLoc, label ~ modifier) ~ body =>
          PCalLabeledStatements(
            PCalLabel(label, modifier).setSourceLocation(labelLoc),
            body,
          )
        }
      }

    override def pcalStmts(using
        ctx: PCalParserContext,
    ): Parser[List[PCalStatement]] =
      pcalUnlabeledStmt.map(List(_)) | pcalLabeledStmt.map(
        List(_),
      ) | pcalCompoundStmt

    override def pcalBody(pSuffix: String)(using
        ctx: PCalParserContext,
    ): Parser[List[PCalStatement]] =
      pcalCompoundStmt

    override def pcalProcessSelf(using
        ctx: PCalParserContext,
    ): Parser[PCalVariableDeclarationBound] =
      "(" ~> ws ~> pcalVarDeclBound <~ ws <~ ")"

    override def pcalAlgorithmOpenBrace(using
        ctx: PCalParserContext,
    ): Parser[Unit] =
      ws ~> "{" ^^^ ()

    override def pcalAlgorithmCloseBrace(using
        ctx: PCalParserContext,
    ): Parser[Unit] =
      ws ~> "}" ^^^ ()
  }

  val pcalPSyntax: PCalPSyntax = new PCalPSyntax {}
  trait PCalPSyntax extends GenericSyntax {
    override def pcalIf(using ctx: PCalParserContext): Parser[PCalIf] = {
      lazy val elsePart: Parser[List[PCalStatement]] = {
        val elsif = withSourceLocation {
          "elsif" ~>! ws ~> tlaExpression ~ (ws ~> "then" ~> ws ~> rep1sep(
            pcalStmt,
            ws,
          )) ~ (ws ~> elsePart) ^^ { case cond ~ yes ~ no =>
            PCalIf(cond, yes, no)
          }
        } ^^ (List(_))
        val els = "else" ~>! ws ~> rep1sep(pcalStmt, ws)

        elsif | els | success(Nil)
      }

      withSourceLocation {
        "if" ~>! ws ~> tlaExpression ~ (ws ~> "then" ~> ws ~> rep1sep(
          pcalStmt,
          ws,
        ) <~ ws) ~ elsePart <~ ws <~ "end" <~ ws <~ "if" ^^ {
          case cond ~ yes ~ no => PCalIf(cond, yes, no)
        }
      }
    }

    override def pcalWhile(using ctx: PCalParserContext): Parser[PCalWhile] =
      withSourceLocation {
        "while" ~>! ws ~> tlaExpression ~ (ws ~> "do" ~> ws ~> rep1sep(
          pcalStmt,
          ws,
        ) <~ ws <~ "end" <~ ws <~ "while") ^^ { case cond ~ body =>
          PCalWhile(cond, body)
        }
      }

    override def pcalEither(using
        ctx: PCalParserContext,
    ): Parser[PCalEither] =
      withSourceLocation {
        "either" ~>! ws ~> rep1sep(
          rep1sep(pcalStmt, ws),
          ws ~> "or" ~> ws,
        ) <~ ws <~ "end" <~ ws <~ "either" ^^ PCalEither.apply
      }

    override def pcalWith(using ctx: PCalParserContext): Parser[PCalWith] =
      withSourceLocation {
        "with" ~>! {
          def rec(rest: Boolean)(using
              ctx: PCalParserContext,
          ): Parser[
            (List[PCalVariableDeclarationBound], List[PCalStatement]),
          ] = {
            val origCtx = ctx
            (if (rest) {
               ws ~> (";" | ",") ~> ws
             } else {
               ws
             }) ~> pcalVarDeclBound.flatMap { decl =>
              given ctx: PCalParserContext = origCtx.withDefinition(decl)
              rec(true) ^^ (p => (decl :: p._1, p._2)) |
                (opt(ws ~> (";" | ",")) ~> ws ~> "do" ~> ws ~> rep1sep(
                  pcalStmt,
                  ws,
                ) <~ ws <~ "end" <~ ws <~ "with") ^^ ((List(decl), _))
            }
          }
          rec(false)
        } ^^ { case (decls, body) =>
          PCalWith(decls, body)
        }
      }

    def pcalStmt(using ctx: PCalParserContext): Parser[PCalStatement] = {
      val labeledStmts: Parser[PCalLabeledStatements] =
        withSourceLocation {
          querySourceLocation {
            tlaIdentifier ~ (ws ~> not(
              ":=",
            ) ~> ":" ~> ws ~> ("+" ^^^ PCalLabel.PlusModifier | "-" ^^^ PCalLabel.MinusModifier | success(
              PCalLabel.NoModifier,
            )))
          } ~! (ws ~> rep1sep(
            pcalUnlabeledStmt,
            ws ~> ";" ~> ws,
          ) <~ ws <~ ";") ^^ { case (labelLoc, label ~ mod) ~ stmts =>
            PCalLabeledStatements(
              PCalLabel(label, mod).setSourceLocation(labelLoc),
              stmts,
            )
          }
        }

      (pcalUnlabeledStmt <~ ws <~ ";") | labeledStmts
    }

    override def pcalStmts(using
        ctx: PCalParserContext,
    ): Parser[List[PCalStatement]] = rep1sep(pcalStmt, ws)

    override def pcalBody(pSuffix: String)(using
        ctx: PCalParserContext,
    ): Parser[List[PCalStatement]] =
      "begin" ~>! ws ~> pcalStmts <~ ws <~ "end" <~ ws <~ pSuffix

    override def pcalProcessSelf(using
        ctx: PCalParserContext,
    ): Parser[PCalVariableDeclarationBound] = pcalVarDeclBound

    override def pcalAlgorithmOpenBrace(using
        ctx: PCalParserContext,
    ): Parser[Unit] = not(ws ~> "{")

    override def pcalAlgorithmCloseBrace(using
        ctx: PCalParserContext,
    ): Parser[Unit] = success(())
  }

  def pcalAlgorithm(using ctx: PCalParserContext): Parser[PCalAlgorithm] =
    pcalPSyntax.pcalAlgorithm | pcalCSyntax.pcalAlgorithm
}

object PCalParser extends PCalParser with ParsingUtils {
  def readAlgorithm(
      underlying: SourceLocation.UnderlyingText,
      contents: CharSequence,
      tlaModule: TLAModule,
  ): PCalAlgorithm = {
    given tlaCtx: TLAParserContext =
      tlaModule
        .moduleDefinitions(captureLocal = true)
        .foldLeft(
          BuiltinModules.Intrinsics.members
            .foldLeft(TLAParserContext(underlying))(_.withDefinition(_)),
        )(_.withDefinition(_))
    given ctx: PCalParserContext = PCalParserContext()
    checkResult(
      phrase(findInComment("fair" | "algorithm", pcalAlgorithm))(
        buildReader(contents, underlying),
      ),
    )
  }
}
