package pgo.parser

import pgo.model.Definition.ScopeIdentifierName
import pgo.model.{
  Definition,
  DefinitionOne,
  RefersTo,
  SourceLocatable,
  SourceLocation,
  SourceLocationWithUnderlying,
  Visitable,
}
import pgo.model.tla._
import pgo.util.ById
import pgo.util.Description.d

import scala.util.parsing.combinator.RegexParsers

trait TLAParser extends RegexParsers {
  override def skipWhitespace: Boolean = false
  val anything: Parser[Unit] = accept("anything", { case _ => () })

  def checkMinColumn(using ctx: TLAParserContext): Parser[Unit] = { in =>
    val lcIn = in.asInstanceOf[LineColumnAwareCharReader]
    if (lcIn.column < ctx.minColumn) {
      Failure(
        s"insufficient indentation ${lcIn.column}, expected at least ${ctx.minColumn}",
        in,
      )
    } else {
      Success((), in)
    }
  }

  def querySourceLocation[T](p: Parser[T]): Parser[(SourceLocation, T)] = {
    final case class GetSourceLocation[T](value: T) extends SourceLocatable
    withSourceLocation(p.map(GetSourceLocation(_))).map {
      case getter @ GetSourceLocation(value) =>
        (getter.sourceLocation, value)
    }
  }

  def withSourceLocation[T <: SourceLocatable](p: => Parser[T]): Parser[T] = {
    lazy val pp: Parser[T] = p // ensure p is evaluated at-most-once
    (in: Input) => {
      val lcIn = in.asInstanceOf[LineColumnAwareCharReader]
      pp(in).flatMapWithNext[T]((t: T) =>
        (nextIn: Input) => {
          val lcNextIn = nextIn.asInstanceOf[LineColumnAwareCharReader]
          Success(
            t.setSourceLocation(
              SourceLocation(
                lcIn.underlyingText,
                startOffset = lcIn.offset,
                endOffset = lcNextIn.offset,
                startLine = lcIn.line,
                endLine = lcNextIn.line,
                startColumn = lcIn.column,
                endColumn = lcNextIn.column,
              ),
            ),
            nextIn,
          )
        },
      )
    }
  }

  final implicit class SymbolParser(sym: TLASymbol.Symbol)
      extends Parser[TLASymbol] {
    private lazy val underlying = withSourceLocation {
      sym.representations.foldRight(failure(s"expected $sym"): Parser[String])(
        _ | _,
      ) ^^ (_ => TLASymbol(sym))
    }
    override def apply(in: Input): ParseResult[TLASymbol] = underlying(in)
  }

  val tlaLineComment: Parser[Unit] =
    ("\\*" ~ rep(acceptIf(_ != '\n')(c => s"'$c' was a new line"))) ^^^ ()

  val tlaMultilineComment: Parser[Unit] = {
    val body = rep1(not("(*" | "*)" | "\\*") ~> anything)
    ("(*" ~ rep {
      tlaMultilineComment | tlaLineComment | body
    } ~ "*)") ^^^ ()
  }

  val tlaWhitespace: Parser[Unit] =
    rep(regex(raw"\s+".r) | tlaMultilineComment | tlaLineComment).map(_ => ())

  def wsChk(using ctx: TLAParserContext): Parser[Unit] =
    tlaWhitespace ~ checkMinColumn ^^^ ()

  val tlaIdentifier: Parser[String] = {
    val identRegex = raw"(?!WF_)(?!SF_)[a-z0-9_A-Z]*[a-zA-Z][a-z0-9_A-Z]*".r

    regex(identRegex) ^? (
      {
        case candidate
            if !TLAMeta.reservedWords.contains(candidate) &&
              !candidate.startsWith("WF_") &&
              !candidate.startsWith("SF_") =>
          candidate
      },
      candidate =>
        s"expected identifier: $candidate is reserved word, or starts with WF_ or SF_",
    )
  }

  val tlaString: Parser[String] =
    elem('\"') ~> (rep[Char] {
      (elem('\\') ~>! {
        elem('\"') | elem(
          '\\',
        ) | ("t" ^^^ '\t') | ("n" ^^^ '\n') | ("f" ^^^ '\f') | ("r" ^^^ '\r')
      }.withFailureMessage(
        "expected valid string escape: one of \\\", \\\\, \\t, \\n, \\f, or \\r",
      )) |
        acceptMatch("string contents", { case c if c != '\"' => c })
    } ^^ { parts => parts.mkString("") }) <~ elem('\"')

  val tlaIdentifierExpr: Parser[TLAIdentifier] =
    withSourceLocation(tlaIdentifier ^^ TLAIdentifier.apply)

  val tlaStringExpr: Parser[TLAString] =
    withSourceLocation(tlaString ^^ TLAString.apply)

  val tlaNumberExpr: Parser[TLANumber] =
    withSourceLocation {
      {
        regex(raw"\d+".r) ^^ { str =>
          (TLANumber.IntValue(BigInt(str)), TLANumber.DecimalSyntax)
        } |
          regex(raw"\d*\.\d+".r) ^^ { str =>
            (TLANumber.DecimalValue(BigDecimal(str)), TLANumber.DecimalSyntax)
          } |
          regex(raw"\\[bB][01]+".r) ^^ { str =>
            (
              TLANumber.IntValue(
                BigInt(str.stripPrefix("\\").stripPrefix("b").stripPrefix("B"), 2),
              ),
              TLANumber.BinarySyntax,
            )
          } |
          regex(raw"\\[oO][0-7]+".r) ^^ { str =>
            (
              TLANumber.IntValue(
                BigInt(str.stripPrefix("\\").stripPrefix("o").stripPrefix("O"), 8),
              ),
              TLANumber.OctalSyntax,
            )
          } |
          regex(raw"\\[hH][0-9a-fA-F]+".r) ^^ { str =>
            (
              TLANumber.IntValue(
                BigInt(str.stripPrefix("\\").stripPrefix("h").stripPrefix("H"), 16),
              ),
              TLANumber.HexadecimalSyntax,
            )
          }
      } ^^ { case (value, syntax) =>
        TLANumber(value, syntax)
      }
    }

  def tlaCommaSep[T](p: => Parser[T])(using
      ctx: TLAParserContext,
  ): Parser[List[T]] =
    repsep(p, wsChk ~> "," <~ wsChk)

  def tlaComma1Sep[T](p: => Parser[T])(using
      ctx: TLAParserContext,
  ): Parser[List[T]] =
    rep1sep(p, wsChk ~> "," <~ wsChk)

  def tlaIdentifierOrTupleQuantifierBound(using
      ctx: TLAParserContext,
  ): Parser[TLAQuantifierBound] = {
    val idOrTuple: Parser[Either[List[TLAIdentifier], TLAIdentifier]] =
      "<<" ~> wsChk ~> tlaCommaSep(tlaIdentifierExpr) <~ wsChk <~ ">>" ^^ (Left(
        _,
      )) | tlaIdentifierExpr ^^ (Right(_))
    withSourceLocation {
      idOrTuple ~ (wsChk ~> "\\in" ~> wsChk ~> tlaExpression) ^^ {
        case Left(ids) ~ set =>
          TLAQuantifierBound(
            TLAQuantifierBound.TupleType,
            ids.map(_.toDefiningIdentifier),
            set,
          )
        case Right(id) ~ set =>
          TLAQuantifierBound(
            TLAQuantifierBound.IdsType,
            List(id.toDefiningIdentifier),
            set,
          )
      }
    }
  }

  def tlaQuantifierBound(using
      ctx: TLAParserContext,
  ): Parser[TLAQuantifierBound] =
    withSourceLocation {
      (("<<" ~> wsChk ~> tlaCommaSep(
        tlaIdentifierExpr,
      ) <~ wsChk <~ ">>" <~ wsChk <~ "\\in") ~ (wsChk ~> tlaExpression)) ^^ {
        case ids ~ set =>
          TLAQuantifierBound(
            TLAQuantifierBound.TupleType,
            ids.map(_.toDefiningIdentifier),
            set,
          )
      } |
        ((tlaComma1Sep(
          tlaIdentifierExpr,
        ) <~ wsChk <~ "\\in") ~ (wsChk ~> tlaExpression)) ^^ { case ids ~ set =>
          TLAQuantifierBound(
            TLAQuantifierBound.IdsType,
            ids.map(_.toDefiningIdentifier),
            set,
          )
        }
    }

  def tlaInstancePrefix(using
      ctx: TLAParserContext,
  ): Parser[List[TLAGeneralIdentifierPart]] = {
    final case class PrefixPart(
        part: TLAGeneralIdentifierPart,
        defn: DefinitionOne,
    ) extends SourceLocatable {
      override def setSourceLocation(
          sourceLocation: SourceLocation,
      ): this.type = {
        part.setSourceLocation(sourceLocation)
        super.setSourceLocation(sourceLocation)
      }
    }

    def impl(
        pfx: List[TLAGeneralIdentifierPart],
    ): Parser[List[TLAGeneralIdentifierPart]] = {
      withSourceLocation {
        tlaIdentifierExpr.flatMap { id =>
          ctx.lookupDefinition(
            pfx.map(id => Definition.ScopeIdentifierName(id.id)) :+ Definition
              .ScopeIdentifierName(id),
          ) match {
            case None =>
              failure(
                s"lookup failed for identifier ${pfx
                    .map(_.id.id)
                    .mkString("!")}${if (pfx.nonEmpty) "!" else ""}${id.id}",
              )
            case Some(defn) =>
              if (defn.arity == 0) {
                // the extra negation is to avoid matching parts of an EXCEPT expression, where an id might be followed by !
                wsChk ~> "!" ~> not(
                  wsChk ~> "[" ~> tlaWhitespace,
                ) ^^^ PrefixPart(TLAGeneralIdentifierPart(id, Nil), defn)
              } else {
                wsChk ~> "(" ~> wsChk ~> tlaComma1Sep(
                  tlaExpression,
                ) <~ wsChk <~ ")" <~ wsChk <~ "!" <~ not(
                  wsChk ~> "[" ~> tlaWhitespace,
                ) ^^ { args =>
                  PrefixPart(TLAGeneralIdentifierPart(id, args), defn)
                }
              }
          }
        }
      }.flatMap { case PrefixPart(idPart, defn) =>
        if (!defn.isModuleInstance) {
          throw KindMismatchError(
            idPart.sourceLocation,
            d"expected module instance, found ${defn.canonicalIdString}",
          )
          // failure(s"kind mismatch: expected module instance, found operator or variable `${defn.identifier.asInstanceOf[ScopeIdentifierName].name.id}`")
        }
        if (idPart.parameters.length != defn.arity) {
          throw ArityMismatchError(
            idPart.sourceLocation,
            defn,
            idPart.parameters.length,
          )
          // failure(s"arity mismatch: definition has arity ${defn.arity}, mismatched with ${idPart.parameters.length}")
        }
        val path = pfx :+ idPart
        opt(wsChk ~> impl(path)) ^^ (_.getOrElse(path))
      }
    }

    (impl(Nil) | success(Nil)).withFailureMessage("expected instance prefix")
  }

  def tlaTupleExpr(using ctx: TLAParserContext): Parser[TLATuple] =
    withSourceLocation {
      "<<" ~> wsChk ~> tlaCommaSep(
        tlaExpression,
      ) <~ wsChk <~ ">>" ^^ TLATuple.apply
    }

  def tlaRequiredActionExpr(using
      ctx: TLAParserContext,
  ): Parser[TLARequiredAction] =
    withSourceLocation {
      ("<<" ~> wsChk ~> tlaExpression <~ wsChk <~ ">>_") ~! (wsChk ~> tlaExpression) ^^ {
        case body ~ vars => TLARequiredAction(body, vars)
      }
    }

  def tlaOperatorCallOrGeneralIdentifier(using
      ctx: TLAParserContext,
  ): Parser[TLAExpression] =
    withSourceLocation {
      (tlaInstancePrefix ~ (not(wsChk ~> "[") ~> wsChk ~> tlaIdentifierExpr))
        .flatMap { case pfx ~ id =>
          val name = Definition.ScopeIdentifierName(id)
          ctx.lookupDefinition(
            pfx.map(id => Definition.ScopeIdentifierName(id.id)) :+ name,
          ) match {
            case None =>
              if (ctx.lateBindingStack > 0 && pfx.isEmpty) {
                // if the context allows late bindings (i.e names bound to the right)
                // then assume arity == 0 and expect whoever incremented lateBindingStack to gather and handle
                // the unbound identifier
                success(TLAGeneralIdentifier(id, Nil))
              } else {
                // don't fail hard; it's possible that the prefix is empty and the identifier is an ambiguous
                // prefix of some other piece of syntax; perhaps an OpDecl
                failure(
                  s"lookup failed for identifier ${pfx
                      .map(_.id.id)
                      .mkString("!")}${if (pfx.nonEmpty) "!" else ""}${id.id}",
                )
              }
            case Some(defn) =>
              if (defn.arity > 0) {
                (wsChk ~> "(" ~> wsChk ~> repsep(
                  tlaExpression.map(
                    Left(_),
                  ) | ((tlaInfixOperator | tlaPrefixOperator | tlaPostfixOperator)
                    .map(Left(_)) | tlaIdentifierExpr.map(Right(_)))
                    .map(Right(_)),
                  wsChk ~> "," <~ wsChk,
                ) <~ wsChk <~ ")") ^^ { args =>
                  if (defn.arity != args.size) {
                    throw ArityMismatchError(id.sourceLocation, defn, args.size)
                  }
                  TLAOperatorCall(
                    name,
                    pfx,
                    args.map:
                      case Left(expr)       => expr
                      case Right(Left(sym)) =>
                        // FIXME: this is completely wrong, but correct version needs a more complex AST
                        // for operator calls
                        TLAString(sym.symbol.stringReprUsage).setSourceLocation(
                          sym.sourceLocation,
                        )
                      case Right(Right(ident)) =>
                        // FIXME: see above
                        TLAString(ident.id).setSourceLocation(
                          ident.sourceLocation,
                        ),
                  ).setRefersTo(defn)
                }
              } else {
                if (defn.arity != 0) {
                  throw ArityMismatchError(id.sourceLocation, defn, 0)
                }
                success(TLAGeneralIdentifier(id, pfx).setRefersTo(defn))
              }
          }
        }
    }

  def tlaConjunctOrDisjunct(
      which: String,
  )(using ctx: TLAParserContext): Parser[TLAExpression] = {
    val origCtx = ctx
    guard(querySourceLocation(which)).flatMap { (locAny, _) =>
      val loc = locAny.asInstanceOf[SourceLocationWithUnderlying]
      val lCtx = origCtx.withMinColumn(loc.startColumn)
      val rCtx = origCtx.withMinColumn(loc.startColumn + 1)
      given ctx: TLAParserContext = rCtx
      rep1({
        given ctx: TLAParserContext = lCtx
        wsChk ~> querySourceLocation(which)
      } ~ (wsChk ~> tlaExpression)) ^^ { parts =>
        val (_, resultExpr) =
          parts.tail.foldLeft((parts.head._1._1, parts.head._2)) {
            (acc, part) =>
              val (locationAcc, lhs) = acc
              val (symLoc, _) ~ rhs = part
              val combinedLoc = locationAcc ++ rhs.sourceLocation
              val sym =
                TLASymbol(TLASymbol.forString(which)).setSourceLocation(symLoc)
              val binop = TLAOperatorCall(
                Definition.ScopeIdentifierSymbol(sym),
                Nil,
                List(lhs, rhs),
              )
                .setSourceLocation(combinedLoc)
              // should always succeed, /\ and \/ are built-in
              binop.setRefersTo(
                ctx
                  .lookupDefinition(List(Definition.ScopeIdentifierSymbol(sym)))
                  .get,
              )
              (combinedLoc, binop)
          }
        resultExpr
      }
    }
  }

  def tlaConjunctExpr(using ctx: TLAParserContext): Parser[TLAExpression] =
    tlaConjunctOrDisjunct("/\\")

  def tlaDisjunctExpr(using ctx: TLAParserContext): Parser[TLAExpression] =
    tlaConjunctOrDisjunct("\\/")

  def tlaIfExpr(using ctx: TLAParserContext): Parser[TLAIf] =
    withSourceLocation {
      ("IF" ~>! wsChk ~> tlaExpression) ~ (wsChk ~> "THEN" ~>! wsChk ~> tlaExpression) ~
        (wsChk ~> "ELSE" ~>! wsChk ~> tlaExpression) ^^ {
          case cond ~ yes ~ no => TLAIf(cond, yes, no)
        }
    }

  def tlaCaseExpr(using ctx: TLAParserContext): Parser[TLACase] =
    withSourceLocation {
      locally {
        withSourceLocation {
          "CASE" ~>! wsChk ~> tlaExpression ~ (wsChk ~> "->" ~> wsChk ~> tlaExpression) ^^ {
            case cond1 ~ res1 => TLACaseArm(cond1, res1)
          }
        } ~
          (wsChk ~> repsep(
            withSourceLocation(
              "[]" ~> wsChk ~> tlaExpression ~ (wsChk ~> "->" ~> wsChk ~> tlaExpression) ^^ {
                case cond ~ res => TLACaseArm(cond, res)
              },
            ),
            wsChk,
          )) ~
          opt(
            wsChk ~> "[]" ~> wsChk ~> "OTHER" ~>! wsChk ~> "->" ~> wsChk ~> tlaExpression,
          )
      } ^^ { case arm1 ~ arms ~ other =>
        TLACase(arm1 :: arms, other)
      }
    }

  def tlaFunctionExpr(using ctx: TLAParserContext): Parser[TLAFunction] = {
    val origCtx = ctx
    withSourceLocation {
      ("[" ~> wsChk ~> tlaComma1Sep(
        tlaQuantifierBound,
      ) <~ wsChk <~ "|->" <~! wsChk).flatMap { bounds =>
        given ctx: TLAParserContext =
          bounds.foldLeft(origCtx)(_.withDefinition(_))
        (tlaExpression <~ wsChk <~ "]") ^^ ((bounds, _))
      } ^^ { case (qbs, expr) =>
        TLAFunction(qbs, expr)
      }
    }
  }

  def tlaRecordSetExpr(using ctx: TLAParserContext): Parser[TLARecordSet] =
    withSourceLocation {
      "[" ~> wsChk ~> tlaComma1Sep {
        withSourceLocation {
          tlaIdentifierExpr ~ (wsChk ~> ":" ~>! wsChk ~> tlaExpression) ^^ {
            case name ~ set => TLARecordSetField(name, set)
          }
        }
      } <~ wsChk <~ "]" ^^ TLARecordSet.apply
    }

  def tlaRecordConstructorExpr(using
      ctx: TLAParserContext,
  ): Parser[TLARecordConstructor] =
    withSourceLocation {
      "[" ~> wsChk ~> tlaComma1Sep {
        withSourceLocation {
          tlaIdentifierExpr ~ (wsChk ~> "|->" ~>! wsChk ~> tlaExpression) ^^ {
            case label ~ value => TLARecordConstructorField(label, value)
          }
        }
      } <~ wsChk <~ "]" ^^ TLARecordConstructor.apply
    }

  def tlaFunctionSetExpr(using
      ctx: TLAParserContext,
  ): Parser[TLAFunctionSet] =
    withSourceLocation {
      "[" ~> wsChk ~> tlaExpression ~ (wsChk ~> "->" ~>! wsChk ~> tlaExpression <~ wsChk <~ "]") ^^ {
        case from ~ to => TLAFunctionSet(from, to)
      }
    }

  def tlaMaybeActionExpr(using
      ctx: TLAParserContext,
  ): Parser[TLAMaybeAction] =
    withSourceLocation {
      "[" ~> wsChk ~> tlaExpression ~ (wsChk ~> "]_" ~>! wsChk ~> tlaExpression) ^^ {
        case body ~ vars => TLAMaybeAction(body, vars)
      }
    }

  def tlaFunctionSubstitutionAtExpr(using
      ctx: TLAParserContext,
  ): Parser[TLAFunctionSubstitutionAt] =
    querySourceLocation("@") ^^ { case (loc, _) =>
      ctx.functionSubstitutionPairAnchor match {
        case None =>
          throw FunctionSubstitutionAtError(loc)
        case Some(anchor) =>
          TLAFunctionSubstitutionAt()
            .setSourceLocation(loc)
            .setRefersTo(anchor)
      }
    }

  def tlaFunctionSubstitutionExpr(using
      ctx: TLAParserContext,
  ): Parser[TLAFunctionSubstitution] =
    withSourceLocation {
      val origCtx = ctx
      "[" ~> wsChk ~> tlaExpression ~ (wsChk ~> "EXCEPT" ~>! wsChk ~> tlaComma1Sep {
        withSourceLocation {
          "!" ~>! rep1 {
            wsChk ~> (withSourceLocation {
              "." ~> wsChk ~> tlaIdentifierExpr ^^ { (id: TLAIdentifier) =>
                TLAFunctionSubstitutionKey(
                  List(TLAString(id.id).setSourceLocation(id.sourceLocation)),
                )
              }
            } |
              withSourceLocation {
                "[" ~> wsChk ~> tlaComma1Sep(
                  tlaExpression,
                ) <~ wsChk <~ "]" ^^ TLAFunctionSubstitutionKey.apply
              })
          }.flatMap { path =>
            val anchor = TLAFunctionSubstitutionPairAnchor() // definition for the @ expression
              .setSourceLocation(path.view.map(_.sourceLocation).reduce(_ ++ _))
            given ctx: TLAParserContext =
              origCtx.withFunctionSubstitutionPairAnchor(anchor)
            (wsChk ~> "=" ~> wsChk ~> tlaExpression) ^^ { value =>
              TLAFunctionSubstitutionPair(anchor, path, value)
            }
          }
        }
      } <~ wsChk <~ "]") ^^ { case fn ~ pairs =>
        TLAFunctionSubstitution(fn, pairs)
      }
    }

  def tlaQuantifiedExistentialExpr(using
      ctx: TLAParserContext,
  ): Parser[TLAQuantifiedExistential] = {
    val origCtx = ctx
    withSourceLocation {
      ("\\E" ~> wsChk ~> tlaComma1Sep(tlaQuantifierBound)).flatMap(bounds => {
        given ctx: TLAParserContext =
          bounds.foldLeft(origCtx)(_.withDefinition(_))
        (wsChk ~> ":" ~>! wsChk ~> tlaExpression) ^^ ((bounds, _))
      }) ^^ { case (bounds, predicate) =>
        TLAQuantifiedExistential(bounds, predicate)
      }
    }
  }

  def tlaQuantifiedUniversalExpr(using
      ctx: TLAParserContext,
  ): Parser[TLAQuantifiedUniversal] = {
    val origCtx = ctx
    withSourceLocation {
      ("\\A" ~> wsChk ~> tlaComma1Sep(tlaQuantifierBound)).flatMap { bounds =>
        given ctx: TLAParserContext =
          bounds.foldLeft(origCtx)(_.withDefinition(_))
        wsChk ~> ":" ~>! wsChk ~> tlaExpression ^^ ((bounds, _))
      } ^^ { case (bounds, predicate) =>
        TLAQuantifiedUniversal(bounds, predicate)
      }
    }
  }

  def tlaUnquantifiedExistentialExpr(using
      ctx: TLAParserContext,
  ): Parser[TLAExistential] = {
    val origCtx = ctx
    withSourceLocation {
      (("\\EE" | "\\E") ~> wsChk ~> tlaComma1Sep(tlaIdentifierExpr))
        .map(_.map(_.toDefiningIdentifier))
        .flatMap { ids =>
          given ctx: TLAParserContext =
            ids.foldLeft(origCtx)(_.withDefinition(_))
          wsChk ~> ":" ~>! wsChk ~> tlaExpression ^^ ((ids, _))
        } ^^ { case (ids, predicate) =>
        TLAExistential(ids, predicate)
      }
    }
  }

  def tlaUnquantifiedUniversalExpr(using
      ctx: TLAParserContext,
  ): Parser[TLAUniversal] = {
    val origCtx = ctx
    withSourceLocation {
      (("\\AA" | "\\A") ~> wsChk ~> tlaComma1Sep(tlaIdentifierExpr))
        .map(_.map(_.toDefiningIdentifier))
        .flatMap { ids =>
          given ctx: TLAParserContext =
            ids.foldLeft(origCtx)(_.withDefinition(_))
          wsChk ~> ":" ~>! wsChk ~> tlaExpression ^^ ((ids, _))
        } ^^ { case (ids, predicate) =>
        TLAUniversal(ids, predicate)
      }
    }
  }

  def tlaSetConstructorExpr(using
      ctx: TLAParserContext,
  ): Parser[TLASetConstructor] =
    withSourceLocation {
      "{" ~> wsChk ~> tlaCommaSep(
        tlaExpression,
      ) <~ wsChk <~ "}" ^^ TLASetConstructor.apply
    }

  def tlaSetRefinementExpr(using
      ctx: TLAParserContext,
  ): Parser[TLASetRefinement] =
    withSourceLocation {
      val origCtx = ctx
      ("{" ~> wsChk ~> tlaIdentifierOrTupleQuantifierBound <~ wsChk <~ ":")
        .flatMap { binding =>
          given ctx: TLAParserContext = origCtx.withDefinition(binding)
          (wsChk ~> tlaExpression <~ wsChk <~ "}") ^^ ((binding, _))
        } ^^ { case (binding, whenExpr) =>
        TLASetRefinement(binding, whenExpr)
      }
    }

  def tlaSetComprehensionExpr(using
      ctx: TLAParserContext,
  ): Parser[TLASetComprehension] = {
    val origCtx = ctx
    withSourceLocation {
      ("{" ~> wsChk ~> {
        given ctx: TLAParserContext = origCtx.withLateBinding
        tlaExpression <~ wsChk <~ ":"
      }) ~ (wsChk ~> tlaComma1Sep(tlaQuantifierBound) <~ wsChk <~ "}") ^^ {
        case expr ~ bounds =>
          // extract all late bindings from bounds, and match them up
          val defns: List[DefinitionOne] =
            bounds.flatMap(bind => bind.singleDefinitions)
          ctx.resolveLateBindings(expr, defns = defns)

          TLASetComprehension(expr, bounds)
      }
    }
  }

  def tlaLetExpr(using ctx: TLAParserContext): Parser[TLALet] =
    withSourceLocation {
      "LET" ~>! wsChk ~> {
        def impl(pfx: List[TLAUnit & Definition])(using
            ctx: TLAParserContext,
        ): Parser[(List[TLAUnit & Definition], TLAExpression)] = {
          val origCtx = ctx
          (tlaOperatorDefinition(isLocal = false) | tlaFunctionDefinition(
            isLocal = false,
          ) | tlaModuleDefinition(isLocal = false)).flatMap {
            (defn: TLAUnit & Definition) =>
              given ctx: TLAParserContext = origCtx.withDefinition(defn)
              val nextPfx = pfx :+ defn
              wsChk ~> (impl(nextPfx) | (("IN" ~>! wsChk ~> tlaExpression) ^^ ((
                nextPfx,
                _,
              ))))
          }
        }
        impl(Nil)
      } ^^ { case (units, body) =>
        TLALet(units, body)
      }
    }

  def tlaFairnessConstraintExpr(using
      ctx: TLAParserContext,
  ): Parser[TLAFairness] =
    withSourceLocation {
      ("WF_" ^^^ TLAFairness.WeakFairness | "SF_" ^^^ TLAFairness.StrongFairness) ~!
        (wsChk ~> tlaExpression) ~!
        (wsChk ~> "(" ~> wsChk ~>! tlaExpression <~ wsChk <~ ")") ^^ {
          case tpe ~ vars ~ expr => TLAFairness(tpe, vars, expr)
        }
    }

  def tlaChooseExpr(using ctx: TLAParserContext): Parser[TLAChoose] =
    withSourceLocation {
      val origCtx = ctx
      ("CHOOSE" ~> wsChk ~> (tlaIdentifierExpr.map(
        Left(_),
      ) | "<<" ~> wsChk ~> tlaCommaSep(tlaIdentifierExpr).map(
        Right(_),
      ) <~ wsChk <~ ">>") <~ wsChk <~ ":" <~ wsChk).flatMap { ids =>
        val definingIds =
          ids.fold(List(_), identity).map(_.toDefiningIdentifier)
        val tpe = ids match {
          case Left(_)  => TLAChoose.Id
          case Right(_) => TLAChoose.Tuple
        }
        given ctx: TLAParserContext =
          definingIds.foldLeft(origCtx)(_.withDefinition(_))
        tlaExpression ^^ (TLAChoose(definingIds, tpe, _))
      }
    }

  def tlaQuantifiedChooseExpr(using
      ctx: TLAParserContext,
  ): Parser[TLAQuantifiedChoose] =
    withSourceLocation {
      val origCtx = ctx
      ("CHOOSE" ~> wsChk ~> tlaQuantifierBound <~ wsChk <~ ":" <~ wsChk)
        .flatMap { binding =>
          given ctx: TLAParserContext = origCtx.withDefinition(binding)
          tlaExpression ^^ (TLAQuantifiedChoose(binding, _))
        }
    }

  def tlaLambda(using ctx: TLAParserContext): Parser[TLALambda] =
    withSourceLocation:
      val origCtx = ctx
      ("LAMBDA" ~> wsChk ~> rep1sep(
        tlaIdentifierExpr.map(_.toDefiningIdentifier) <~ wsChk,
        "," ~> wsChk,
      ) <~ ":" <~ wsChk).flatMap: bindings =>
        given ctx: TLAParserContext =
          bindings.foldLeft(origCtx)(_.withDefinition(_))
        tlaExpression ^^ (TLALambda(bindings, _))
  end tlaLambda

  val tlaPrefixOperator: Parser[TLASymbol] =
    withSourceLocation {
      TLAMeta.prefixOperators.keys.toList.sorted
        .sortWith(_.length > _.length)
        .foldRight(failure("not a prefix operator"): Parser[TLASymbol]) {
          (pfx, otherwise) =>
            if (pfx == "-_") { // special-case the syntactic anomaly that is "-"
              "-" ^^^ TLASymbol(TLASymbol.forString("-_")) | otherwise
            } else {
              pfx ^^^ TLASymbol(TLASymbol.forString(pfx)) | otherwise
            }
        }
    }

  // same as tlaPrefixOperator, but will read -. instead of just -
  val tlaPrefixOperatorDef: Parser[TLASymbol] =
    withSourceLocation {
      TLAMeta.prefixOperators.keys.toList.sorted
        .sortWith(_.length > _.length)
        .foldRight(failure("not a prefix operator"): Parser[TLASymbol]) {
          (pfx, otherwise) =>
            if (pfx == "-_") { // special-case the syntactic anomaly that is "-"
              "-." ^^ (_ => TLASymbol(TLASymbol.forString("-_"))) | otherwise
            } else {
              pfx ^^ (_ => TLASymbol(TLASymbol.forString(pfx))) | otherwise
            }
        }
    }

  private lazy val tlaInfixOperatorV: Parser[TLASymbol] =
    TLAMeta.infixOperators.keys.toList.sorted
      .sortWith(_.length > _.length)
      .foldRight(failure("not an infix operator"): Parser[TLASymbol]) {
        (str, otherwise) =>
          def proc(parser: Parser[?]): Parser[TLASymbol] =
            parser ^^ (_ => TLASymbol(TLASymbol.forString(str))) | otherwise
          str match
            case "=" =>
              proc(
                ("=" - "==")
                  .withFailureMessage("== should not be split into 2 = tokens"),
              )
            case str =>
              proc(str)
      }
  def tlaInfixOperator: Parser[TLASymbol] = tlaInfixOperatorV

  val tlaPostfixOperator: Parser[TLASymbol] =
    TLAMeta.postfixOperators.keys.toList.sorted
      .sortWith(_.length > _.length)
      .foldRight(failure("not a postfix operator"): Parser[TLASymbol]) {
        (str, otherwise) =>
          str ^^ (_ => TLASymbol(TLASymbol.forString(str))) | otherwise
      }

  def tlaExpressionMinPrecedence(
      minPrecedence: Int,
  )(using ctx: TLAParserContext): Parser[TLAExpression] = {
    val lhsWithPrefix = querySourceLocation(
      tlaInstancePrefix ~ (wsChk ~> tlaPrefixOperator),
    ).flatMap { case (loc, pfx ~ opSym) =>
      val (lowPrec, highPrec) =
        (opSym.symbol.precedenceLow, opSym.symbol.precedenceHigh)
      wsChk ~> querySourceLocation(
        tlaExpressionMinPrecedence(highPrec + 1),
      ) ^^ { case (loc2, innerExpr) =>
        val result = TLAOperatorCall(
          Definition.ScopeIdentifierSymbol(opSym),
          pfx,
          List(innerExpr),
        )
          .setSourceLocation(loc ++ loc2)
        ctx.lookupDefinition(
          pfx.map(id => Definition.ScopeIdentifierName(id.id)) :+ Definition
            .ScopeIdentifierSymbol(opSym),
        ) match {
          case None =>
            throw DefinitionLookupError(
              pfx,
              Definition.ScopeIdentifierSymbol(opSym),
            )
          case Some(defn) =>
            assert(defn.arity == 1, s"found prefix operator with arity ${defn.arity}")
            result.setRefersTo(defn)
        }
        result
      }
    } | tlaExpressionNoOperators

    def withPartOpt(
        lhsLoc: SourceLocation,
        lhs: TLAExpression,
        maxPrecedence: Int,
    ): Parser[TLAExpression] =
      withFunctionCall(lhsLoc, lhs, maxPrecedence) |
        withDot(lhsLoc, lhs, maxPrecedence) |
        withCrossProduct(lhsLoc, lhs, maxPrecedence) |
        withInfix(lhsLoc, lhs, maxPrecedence) |
        withPostfix(lhsLoc, lhs, maxPrecedence) |
        success(lhs)

    def withPostfix(
        lhsLoc: SourceLocation,
        lhs: TLAExpression,
        maxPrecedence: Int,
    ): Parser[TLAExpression] =
      querySourceLocation {
        (wsChk ~> tlaInstancePrefix) ~ (wsChk ~> tlaPostfixOperator) ^? (
          {
            case pfx ~ opSym if opSym.symbol.precedence >= minPrecedence =>
              (pfx, opSym)
          },
          { case _ ~ opSym =>
            s"operator ${opSym.symbol.stringReprUsage} used below min precedence ($minPrecedence)"
          },
        )
      }.flatMap { case (loc, (pfx, opSym)) =>
        val combinedLoc = lhsLoc ++ loc
        val result = TLAOperatorCall(
          Definition.ScopeIdentifierSymbol(opSym),
          pfx,
          List(lhs),
        )
          .setSourceLocation(combinedLoc)
        ctx.lookupDefinition(
          pfx.map(id => Definition.ScopeIdentifierName(id.id)) :+ Definition
            .ScopeIdentifierSymbol(opSym),
        ) match {
          case None =>
            throw DefinitionLookupError(
              pfx,
              Definition.ScopeIdentifierSymbol(opSym),
            )
          case Some(defn) => result.setRefersTo(defn)
        }
        withPartOpt(combinedLoc, result, maxPrecedence)
      }

    def withCrossProduct(
        lhsLoc: SourceLocation,
        lhs: TLAExpression,
        maxPrecedence: Int,
    ): Parser[TLAExpression] =
      if (minPrecedence <= 13 && maxPrecedence >= 10) {
        (wsChk ~> rep1sep(
          ("\\X" | "\\times") ~> wsChk ~> tlaExpressionMinPrecedence(14),
          wsChk,
        )).flatMap { elems =>
          val combinedLoc =
            lhsLoc ++ elems.view.map(_.sourceLocation).reduce(_ ++ _)
          val expr = TLACrossProduct(lhs :: elems)
            .setSourceLocation(combinedLoc)
          withPartOpt(combinedLoc, expr, 9)
        }
      } else {
        failure("not in precedence range 10-13")
      }

    def withFunctionCall(
        lhsLoc: SourceLocation,
        lhs: TLAExpression,
        maxPrecedence: Int,
    ): Parser[TLAExpression] =
      if (minPrecedence <= 16) {
        querySourceLocation(
          wsChk ~> "[" ~> wsChk ~> tlaComma1Sep(tlaExpression) <~ wsChk <~ "]",
        ).flatMap { case (loc, args) =>
          val combinedLoc = lhsLoc ++ loc
          withPartOpt(
            combinedLoc,
            TLAFunctionCall(lhs, args).setSourceLocation(combinedLoc),
            15,
          )
        }
      } else {
        failure("not at precedence 16")
      }

    def withDot(
        lhsLoc: SourceLocation,
        lhs: TLAExpression,
        maxPrecedence: Int,
    ): Parser[TLAExpression] =
      if (minPrecedence <= 17) {
        rep1sep(wsChk ~> "." ~> wsChk ~> tlaIdentifierExpr, wsChk).flatMap {
          dots =>
            val (combinedLoc, result) = dots.foldLeft((lhsLoc, lhs)) {
              (acc, dotId) =>
                val (lhsLoc, lhs) = acc
                val combinedLoc = lhsLoc ++ dotId.sourceLocation
                (combinedLoc, TLADot(lhs, dotId).setSourceLocation(combinedLoc))
            }
            withPartOpt(combinedLoc, result, 16)
        }
      } else {
        failure("not at precedence 17")
      }

    def withInfix(
        lhsLoc: SourceLocation,
        lhs: TLAExpression,
        maxPrecedence: Int,
    ): Parser[TLAExpression] =
      querySourceLocation(
        (wsChk ~> tlaInstancePrefix) ~ (wsChk ~> withSourceLocation(
          tlaInfixOperator,
        )) ^? (
          {
            case pfx ~ opSym
                if opSym.symbol.precedenceLow >= minPrecedence && opSym.symbol.precedenceHigh <= maxPrecedence =>
              (pfx, opSym)
          },
          { case _ ~ opSym =>
            s"operator ${opSym.symbol.stringReprUsage} used outside precedence range (min = $minPrecedence, max = $maxPrecedence, actual = ${opSym.symbol.precedenceLow}-${opSym.symbol.precedenceHigh})"
          },
        ),
      ).flatMap { case (loc, (pfx, opSym)) =>
        val (lowPrec, highPrec, leftAssoc) = (
          opSym.symbol.precedenceLow,
          opSym.symbol.precedenceHigh,
          opSym.symbol.isAssociative,
        )
        querySourceLocation(wsChk ~> tlaExpressionMinPrecedence(highPrec + 1))
          .flatMap { case (rhsLoc, rhs) =>
            val combinedLoc = lhsLoc ++ loc ++ rhsLoc
            val result = TLAOperatorCall(
              Definition.ScopeIdentifierSymbol(opSym),
              pfx,
              List(lhs, rhs),
            )
              .setSourceLocation(combinedLoc)
            ctx.lookupDefinition(
              pfx.map(id => Definition.ScopeIdentifierName(id.id)) :+ Definition
                .ScopeIdentifierSymbol(opSym),
            ) match {
              case None =>
                throw DefinitionLookupError(
                  pfx,
                  Definition.ScopeIdentifierSymbol(opSym),
                )
              case Some(defn) => result.setRefersTo(defn)
            }
            if (leftAssoc) {
              def assoc(
                  lhsLoc: SourceLocation,
                  lhs: TLAExpression,
              ): Parser[TLAExpression] =
                querySourceLocation {
                  (wsChk ~> tlaInstancePrefix) ~ (wsChk ~> opSym.symbol) ~ (wsChk ~> tlaExpressionMinPrecedence(
                    highPrec + 1,
                  ))
                }.flatMap { case (loc, pfx ~ opSym ~ rhs) =>
                  val combinedLoc = lhsLoc ++ loc
                  val nextLhs = TLAOperatorCall(
                    Definition.ScopeIdentifierSymbol(opSym),
                    pfx,
                    List(lhs, rhs),
                  )
                    .setSourceLocation(combinedLoc)
                  ctx.lookupDefinition(
                    pfx.map(id =>
                      Definition.ScopeIdentifierName(id.id),
                    ) :+ Definition.ScopeIdentifierSymbol(opSym),
                  ) match {
                    case None =>
                      throw DefinitionLookupError(
                        pfx,
                        Definition.ScopeIdentifierSymbol(opSym),
                      )
                    case Some(defn) => nextLhs.setRefersTo(defn)
                  }
                  assoc(combinedLoc, nextLhs) | withPartOpt(
                    combinedLoc,
                    nextLhs,
                    lowPrec - 1,
                  )
                }
              assoc(combinedLoc, result) | withPartOpt(
                combinedLoc,
                result,
                lowPrec - 1,
              )
            } else {
              withPartOpt(combinedLoc, result, lowPrec - 1)
            }
          }
      }

    querySourceLocation(lhsWithPrefix).flatMap { case (loc, lhs) =>
      withPartOpt(loc, lhs, 18)
    }
  }

  def tlaExpressionNoOperators(using
      ctx: TLAParserContext,
  ): Parser[TLAExpression] =
    tlaNumberExpr |
      tlaStringExpr |
      ("(" ~>! wsChk ~> tlaExpression <~ wsChk <~ ")") |
      tlaFunctionSubstitutionAtExpr |
      tlaTupleExpr |
      tlaRequiredActionExpr |
      tlaOperatorCallOrGeneralIdentifier |
      tlaFairnessConstraintExpr |
      tlaConjunctExpr | tlaDisjunctExpr |
      tlaIfExpr |
      tlaLetExpr |
      tlaCaseExpr |
      // starting with [
      tlaFunctionExpr | tlaRecordSetExpr | tlaRecordConstructorExpr | tlaFunctionSetExpr |
      tlaMaybeActionExpr | tlaFunctionSubstitutionExpr |
      // starting with \E, EE, \A, \AA
      tlaQuantifiedExistentialExpr | tlaQuantifiedUniversalExpr |
      tlaUnquantifiedExistentialExpr | tlaUnquantifiedUniversalExpr |
      // starting with {
      tlaSetRefinementExpr | tlaSetComprehensionExpr | tlaSetConstructorExpr |
      // starting with CHOOSE
      tlaChooseExpr | tlaQuantifiedChooseExpr |
      // starting with LAMBDA
      tlaLambda

  def tlaExpression(using ctx: TLAParserContext): Parser[TLAExpression] =
    tlaExpressionMinPrecedence(0)

  def tlaOpDecl(using ctx: TLAParserContext): Parser[TLAOpDecl] =
    withSourceLocation {
      val named = tlaIdentifierExpr ~ (wsChk ~> "(" ~> tlaComma1Sep(
        "_",
      ) <~ wsChk <~ ")") ^^ { case id ~ args =>
        TLAOpDecl.NamedVariant(id, args.length)
      }
      val id = tlaIdentifierExpr ^^ (TLAOpDecl.NamedVariant(_, 0))
      val prefix =
        tlaPrefixOperatorDef <~ wsChk <~ "_" ^^ TLAOpDecl.SymbolVariant.apply
      val infix =
        "_" ~> wsChk ~> tlaInfixOperator <~ wsChk <~ "_" ^^ TLAOpDecl.SymbolVariant.apply
      val postfix =
        "_" ~> wsChk ~> tlaPostfixOperator ^^ TLAOpDecl.SymbolVariant.apply

      (named | id | prefix | infix | postfix) ^^ (TLAOpDecl(_))
    }

  def tlaOperatorDefinition(
      isLocal: Boolean,
  )(using ctx: TLAParserContext): Parser[TLAOperatorDefinition] = {
    val origCtx = ctx
    val prefix = withSourceLocation {
      (tlaPrefixOperatorDef ~ (wsChk ~> tlaIdentifierExpr)).flatMap {
        case opSym ~ id =>
          val opDecl = TLAOpDecl(TLAOpDecl.NamedVariant(id, 0))
            .setSourceLocation(id.sourceLocation)
          given ctx: TLAParserContext = origCtx.withDefinition(opDecl)
          (wsChk ~> "==" ~> wsChk ~> tlaExpression) ^^ ((opSym, opDecl, _))
      } ^^ { case (opSym, opDecl, body) =>
        TLAOperatorDefinition(
          Definition.ScopeIdentifierSymbol(opSym),
          List(opDecl),
          body,
          isLocal,
        )
      }
    }
    val infix = withSourceLocation {
      (tlaIdentifierExpr ~ (wsChk ~> tlaInfixOperator) ~ (wsChk ~> tlaIdentifierExpr))
        .flatMap { case lhsId ~ opSym ~ rhsId =>
          val lhsOpDecl = TLAOpDecl(TLAOpDecl.NamedVariant(lhsId, 0))
            .setSourceLocation(lhsId.sourceLocation)
          val rhsOpDecl = TLAOpDecl(TLAOpDecl.NamedVariant(rhsId, 0))
            .setSourceLocation(rhsId.sourceLocation)
          given ctx: TLAParserContext =
            origCtx.withDefinition(lhsOpDecl).withDefinition(rhsOpDecl)
          (wsChk ~> "==" ~> wsChk ~> tlaExpression) ^^ ((
            lhsOpDecl,
            opSym,
            rhsOpDecl,
            _,
          ))
        } ^^ { case (lhsOpDecl, opSym, rhsOpDecl, body) =>
        TLAOperatorDefinition(
          Definition.ScopeIdentifierSymbol(opSym),
          List(lhsOpDecl, rhsOpDecl),
          body,
          isLocal,
        )
      }
    }
    val postfix = withSourceLocation {
      (tlaIdentifierExpr ~ (wsChk ~> tlaPostfixOperator)).flatMap {
        case id ~ opSym =>
          val opDecl = TLAOpDecl(TLAOpDecl.NamedVariant(id, 0))
            .setSourceLocation(id.sourceLocation)
          given ctx: TLAParserContext = origCtx.withDefinition(opDecl)
          (wsChk ~> "==" ~> wsChk ~> tlaExpression) ^^ ((opDecl, opSym, _))
      } ^^ { case (opDecl, opSym, body) =>
        TLAOperatorDefinition(
          Definition.ScopeIdentifierSymbol(opSym),
          List(opDecl),
          body,
          isLocal,
        )
      }
    }
    val nonfix = withSourceLocation {
      (tlaIdentifierExpr ~ opt(
        wsChk ~> "(" ~> tlaComma1Sep(tlaOpDecl) <~ wsChk <~ ")",
      ) <~ wsChk <~ "==" <~ wsChk).flatMap {
        case id ~ None => tlaExpression ^^ ((id, Nil, _))
        case id ~ Some(opDecls) =>
          given ctx: TLAParserContext =
            opDecls.foldLeft(origCtx)(_.withDefinition(_))
          tlaExpression ^^ ((id, opDecls, _))
      } ^^ { case (id, opDecls, body) =>
        TLAOperatorDefinition(
          Definition.ScopeIdentifierName(id),
          opDecls,
          body,
          isLocal,
        )
      }
    }

    prefix | infix | postfix | nonfix
  }

  def tlaFunctionDefinition(
      isLocal: Boolean,
  )(using ctx: TLAParserContext): Parser[TLAOperatorDefinition] = {
    val origCtx = ctx
    withSourceLocation {
      querySourceLocation(
        tlaIdentifierExpr ~
          (wsChk ~> "[" ~> wsChk ~> tlaComma1Sep(
            tlaQuantifierBound,
          ) <~ wsChk <~ "]" <~ wsChk <~ "=="),
      ).flatMap { case (loc, id ~ bounds) =>
        val dummyDefn = TLAOperatorDefinition(
          Definition.ScopeIdentifierName(id),
          Nil,
          TLAString(""),
          isLocal,
        )
        given ctx: TLAParserContext =
          bounds.foldLeft(origCtx.withDefinition(dummyDefn))(
            _.withDefinition(_),
          )
        (wsChk ~> tlaExpression) ^^ { body =>
          (dummyDefn, id, TLAFunction(bounds, body).setSourceLocation(loc))
        }
      } ^^ { case (dummyDefn, id, function) =>
        val result = TLAOperatorDefinition(
          Definition.ScopeIdentifierName(id),
          Nil,
          function,
          isLocal,
        )

        // correct any recursive references to the unit being defined
        function.visit(Visitable.BottomUpFirstStrategy):
          case ref @ RefersTo(target) if target eq dummyDefn =>
            ref
              .asInstanceOf[RefersTo[TLAOperatorDefinition]]
              .setRefersTo(result)

        result
      }
    }
  }

  def tlaInstance(
      isLocal: Boolean,
  )(using ctx: TLAParserContext): Parser[TLAInstance] =
    withSourceLocation {
      "INSTANCE" ~> wsChk ~> tlaIdentifierExpr ~
        opt(wsChk ~> "WITH" ~> tlaComma1Sep(withSourceLocation {
          (tlaIdentifierExpr.map(
            Definition.ScopeIdentifierName.apply,
          ) | (tlaPrefixOperatorDef | tlaInfixOperator | tlaPostfixOperator)
            .map(Definition.ScopeIdentifierSymbol.apply)) ~
            (wsChk ~> "<-" ~> wsChk ~> tlaExpression) ^^ { case from ~ to =>
              TLAInstanceRemapping(from, to)
            }
        })).map(_.getOrElse(Nil)) ^^ { case moduleId ~ substitutions =>
          TLAInstance(moduleId, substitutions, isLocal)
        }
    }

  def tlaModuleDefinition(
      isLocal: Boolean,
  )(using ctx: TLAParserContext): Parser[TLAModuleDefinition] =
    withSourceLocation {
      val origCtx = ctx
      (tlaIdentifierExpr ~ opt(
        wsChk ~> "(" ~> tlaComma1Sep(tlaOpDecl) <~ wsChk <~ ")",
      )).flatMap { case id ~ argsOpt =>
        given ctx: TLAParserContext =
          argsOpt.getOrElse(Nil).foldLeft(origCtx)(_.withDefinition(_))
        (wsChk ~> "==" ~> wsChk ~> tlaInstance(isLocal)) ^^ ((
          id,
          argsOpt.getOrElse(Nil),
          _,
        ))
      } ^^ { case (id, args, instance) =>
        TLAModuleDefinition(id, args, instance, isLocal)
      }
    }

  def tlaRecursive(using ctx: TLAParserContext): Parser[TLARecursive] =
    withSourceLocation {
      "RECURSIVE" ~> wsChk ~> tlaComma1Sep(tlaOpDecl) ^^ { decls =>
        // note: setRefersTo will be called when (if) the corresponding operator definition is reached.
        //   tlaModule parsing should catch if there is no such definition
        TLARecursive(
          decls.map(decl =>
            TLARecursive.Decl(decl).setSourceLocation(decl.sourceLocation),
          ),
        )
      }
    }

  private def tlaModuleAbstract(moduleEnd: Parser[Any], carefulWs: Parser[Any])(
      using ctx: TLAParserContext,
  ): Parser[TLAModule] =
    withSourceLocation {
      val origCtx = ctx

      ("----" ~> rep(
        elem('-'),
      ) ~> wsChk ~> "MODULE" ~>! wsChk ~> tlaIdentifierExpr <~ wsChk <~ "----" <~ rep(
        elem('-'),
      )) ~
        opt(
          wsChk ~> "EXTENDS" ~>! wsChk ~> tlaComma1Sep(
            tlaIdentifierExpr,
          ) <~ carefulWs,
        ).flatMap { exts =>
          def unitRec(using ctx: TLAParserContext): Parser[List[TLAUnit]] = {
            val origCtx = ctx
            opt("----" ~> rep(elem('-')) ~> carefulWs) ~> locally {
              moduleEnd.map(_ => Nil)
                | tlaUnit.flatMap { unit =>
                  given ctx: TLAParserContext =
                    unit.definitions.foldLeft(origCtx)(_.withDefinition(_))
                  (carefulWs ~> unitRec ^^ (unit :: _))
                }
            }
          }

          val extensions = exts.getOrElse(Nil)
          given ctx: TLAParserContext = exts
            .getOrElse(Nil)
            .foldLeft(origCtx): (ctx, ext) =>
              ctx
                .lookupModuleDefinitions(Definition.ScopeIdentifierName(ext))
                .foldLeft(ctx)(_.withDefinition(_))
          (carefulWs ~> unitRec) ^^ { units =>
            // resolve all uses of the RECURSIVE directive, which, until this point, is allowed to be used instead
            // of the correct operator definition during scoping.
            // the final outcome here should have no references to TLARecursive.Decl, only references
            // to the operator definition
            units.iterator
              .collect { case TLARecursive(decls) => decls }
              .flatten
              .foreach { decl =>
                if (!decl.hasRefersTo) {
                  throw UnboundRecursiveDeclError(decl)
                }
              }

            // rebind all references to TLARecursive.Decl, now we're sure all RECURSIVE directives _have_ alternative
            // bindings
            units.foreach(_.visit(Visitable.BottomUpFirstStrategy) {
              case node @ RefersTo(decl: TLARecursive.Decl) =>
                node
                  .asInstanceOf[RefersTo[TLAOperatorDefinition]]
                  .setRefersTo(decl.refersTo)
            })

            (extensions, units)
          }
        } ^^ { case name ~ ((exts, units)) =>
          TLAModule(name, exts, units)
        }
    }

  def tlaModule(using ctx: TLAParserContext): Parser[TLAModule] =
    tlaModuleAbstract(
      moduleEnd = wsChk <~ "====" <~ rep(elem('=')),
      carefulWs = wsChk,
    )

  def tlaUnit(using ctx: TLAParserContext): Parser[TLAUnit] = {
    val variableDeclaration: Parser[TLAUnit] = withSourceLocation {
      ("VARIABLES" | "VARIABLE") ~>! wsChk ~> tlaComma1Sep(
        tlaIdentifierExpr.map(_.toDefiningIdentifier),
      ) ^^ TLAVariableDeclaration.apply
    }
    val constantDeclaration: Parser[TLAUnit] = withSourceLocation {
      ("CONSTANTS" | "CONSTANT") ~>! wsChk ~> tlaComma1Sep(
        tlaOpDecl,
      ) ^^ TLAConstantDeclaration.apply
    }
    val assumption: Parser[TLAUnit] = withSourceLocation {
      ("ASSUME" | "ASSUMPTION" | "AXIOM") ~>! wsChk ~> tlaExpression ^^ TLAAssumption.apply
    }
    val theorem: Parser[TLAUnit] = withSourceLocation {
      "THEOREM" ~>! wsChk ~> tlaExpression ^^ TLATheorem.apply
    }

    ("LOCAL" ~>! wsChk ~> {
      tlaInstance(true) | tlaModuleDefinition(true) | tlaFunctionDefinition(
        true,
      ) |
        tlaOperatorDefinition(true)
    }) |
      tlaInstance(false) |
      tlaModuleDefinition(false) |
      tlaFunctionDefinition(false) |
      tlaOperatorDefinition(false) |
      variableDeclaration |
      constantDeclaration |
      assumption |
      theorem |
      tlaRecursive |
      tlaModule
  }

  val findTLAModule: Parser[Unit] =
    rep(not("----") ~> anything) ^^^ ()

  def tlaModuleBeforeTranslation(using
      ctx: TLAParserContext,
  ): Parser[TLAModule] = {
    val translationTag =
      ("\\*" <~ rep("*") <~ rep1(" ") <~ "BEGIN" <~ rep1(" ") <~ "TRANSLATION")
        .withFailureMessage(
          "\\* expected: for scoping reasons, an MPCal-compilable TLA+ module must contain a `\\* BEGIN TRANSLATION` tag",
        )
    val wsWithoutTranslationTag =
      rep(
        regex("""\s+""".r) | tlaMultilineComment | not(
          translationTag,
        ) ~> tlaLineComment,
      )

    tlaModuleAbstract(
      moduleEnd = wsWithoutTranslationTag ~> translationTag,
      carefulWs = wsWithoutTranslationTag,
    )
  }
}

object TLAParser extends TLAParser with ParsingUtils {
  def readExpression(
      underlying: SourceLocation.UnderlyingText,
      seq: CharSequence,
      definitions: Seq[Definition] = Nil,
  ): TLAExpression = {
    given ctx: TLAParserContext = definitions.foldLeft(
      BuiltinModules.Intrinsics.members.foldLeft(TLAParserContext(underlying))(
        _.withDefinition(_),
      ),
    )(_.withDefinition(_))
    checkResult {
      phrase(wsChk ~> tlaExpression <~ wsChk)(buildReader(seq, underlying))
    }
  }

  def readModule(
      underlying: SourceLocation.UnderlyingText,
      seq: CharSequence,
  ): TLAModule = {
    given ctx: TLAParserContext =
      BuiltinModules.Intrinsics.members.foldLeft(TLAParserContext(underlying))(
        _.withDefinition(_),
      )
    checkResult(
      phrase(
        findTLAModule ~> tlaModule <~ rep(accept("anything", { case _ => () })),
      )(buildReader(seq, underlying)),
    )
  }

  def readModuleBeforeTranslation(
      underlying: SourceLocation.UnderlyingText,
      seq: CharSequence,
  ): TLAModule = {
    given ctx: TLAParserContext =
      BuiltinModules.Intrinsics.members.foldLeft(TLAParserContext(underlying))(
        _.withDefinition(_),
      )
    checkResult(
      phrase(
        findTLAModule ~> tlaModuleBeforeTranslation <~ rep(
          accept("anything", { case _ => () }),
        ),
      )(buildReader(seq, underlying)),
    )
  }
}
