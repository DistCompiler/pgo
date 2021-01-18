package pgo.parser

import pgo.model.tla._
import pgo.util.SourceLocation

import scala.annotation.tailrec
import scala.collection.mutable
import scala.jdk.CollectionConverters._
import scala.util.parsing.combinator.RegexParsers
import scala.util.parsing.input.Reader

final case class TLAParserContext(minColumn: Int = -1,
                                  lateBindingStack: List[mutable.Map[TLAIdentifier,mutable.Buffer[TLADefinitionOne=>Unit]]] = Nil,
                                  currentScope: Map[TLAIdentifier,TLADefinitionOne] = Map.empty) {
  def withMinColumn(minColumn: Int): TLAParserContext =
    copy(minColumn=minColumn)

  def withDefinition(defn: TLADefinition): TLAParserContext =
    defn match {
      case builtin: TLABuiltinModules.TLABuiltinOperator => // special case: builtins have aliases that refer to the same op
        copy(currentScope=builtin.aliasIDs.foldLeft(currentScope.updated(builtin.identifier, builtin)) { (currentScope, id) =>
          currentScope.updated(id, builtin)
        })
      case defn: TLADefinitionOne => copy(currentScope=currentScope.updated(defn.identifier, defn))
      case composite: TLADefinitionComposite => composite.members.foldLeft(this)(_.withDefinition(_))
    }

  def withSelf(loc: SourceLocation, defn: TLADefinitionOne): TLAParserContext =
    copy(currentScope=currentScope.updated(new TLAIdentifier(loc, "self"), defn))

  def withLateBinding: TLAParserContext =
    copy(lateBindingStack=mutable.Map.empty[TLAIdentifier,mutable.Buffer[TLADefinitionOne=>Unit]] :: lateBindingStack)

  def lookupModuleExtends(id: TLAIdentifier): TLAModuleExtends =
    currentScope.get(id) match {
      case Some(defn: TLAModule) => TLAModuleExtendsModule(defn)
      case Some(defn) => throw DoesNotExtendAModuleError(id.getLocation, id, defn)
      case None => TLABuiltinModules.builtinModules.get(id) match {
        case Some(builtin) => TLAModuleExtendsBuiltin(builtin)
        case None => throw ModuleNotFoundError(id.getLocation, id)
      }
    }

  def instantiateModule(id: TLAIdentifier): TLAParserContext = {
    currentScope.get(id) match {
      case Some(defn: TLAModule) => ???
      case _ => ???
    }
  }

  def lookupDefinition(path: List[TLAIdentifier]): Option[TLADefinitionOne] = {
    path match {
      case Nil => None
      case List(id) => currentScope.get(id)
      case id :: tl =>
        currentScope.get(id).flatMap(lookupDefinition(_, tl))
    }
  }

  @tailrec
  private def lookupDefinition(defn: TLADefinitionOne, path: List[TLAIdentifier]): Option[TLADefinitionOne] =
    path match {
      case Nil => None
      case List(id) => defn.scope.get(id)
      case hd :: tl =>
        defn.scope.get(hd) match {
          case None => None
          case Some(defn) => lookupDefinition(defn, tl)
        }
    }
}

trait TLAParser extends RegexParsers {
  override def skipWhitespace: Boolean = false
  val anything: Parser[Unit] = accept("anything", { case _ => () })

  def checkMinColumn(implicit ctx : TLAParserContext) : Parser[Unit] = (in: Reader[Char]) => {
    val lcIn = in.asInstanceOf[LineColumnAwareCharReader]
    if (lcIn.column < ctx.minColumn) {
      Failure(s"insufficient indentation ${lcIn.column}, expected at least ${ctx.minColumn}", in)
    } else {
      Success((), in)
    }
  }

  def withSourceLocation[T](p : =>Parser[T]) : Parser[(SourceLocation, T)] = {
    lazy val pp = p // ensure p is evaluated at-most-once
    (in: Reader[Char]) => {
      val lcIn = in.asInstanceOf[LineColumnAwareCharReader]
      pp.apply(in).flatMapWithNext { t => in: Reader[Char] =>
        val lcNextIn = in.asInstanceOf[LineColumnAwareCharReader]
        Success(
          (new SourceLocation(lcIn.path, lcIn.offset, lcNextIn.offset, lcIn.line, lcNextIn.line, lcIn.column, lcNextIn.column), t),
          in)
      }
    }
  }

  val tlaLineComment : Parser[Unit] =
    ("\\*" ~ rep(acceptIf(_ != '\n')(c => s"'$c' was a new line"))) ^^^ ()

  val tlaMultilineComment : Parser[Unit] = {
    val body = rep1(not("(*" | "*)" | "\\*") ~> acceptIf(_ => true)(_ => ???))
    ("(*" ~ rep {
      tlaMultilineComment | tlaLineComment | body
    } ~ "*)") ^^^ ()
  }

  val tlaWhitespace : Parser[Unit] = rep(regex(raw"\s+".r) | tlaMultilineComment | tlaLineComment).map(_ => ())

  def wsChk(implicit ctx: TLAParserContext): Parser[Unit] = tlaWhitespace ~ checkMinColumn ^^^ ()

  val tlaIdentifier : Parser[String] = {
    val identRegex = raw"(?!WF_)(?!SF_)[a-z0-9_A-Z]*[a-zA-Z][a-z0-9_A-Z]*".r

    regex(identRegex) ^? ({
      case candidate if !TLAMeta.reservedWords.contains(candidate) &&
        !candidate.startsWith("WF_") &&
        !candidate.startsWith("SF_") => candidate
    }, candidate => s"expected identifier: $candidate is reserved word, or starts with WF_ or SF_")
  }

  val tlaString : Parser[String] =
    elem('\"') ~> (rep[Char] {
      (elem('\\') ~>! {
        elem('\"') | elem('\\') | ("t" ^^^ '\t') | ("n" ^^^ '\n') | ("f" ^^^ '\f') | ("r" ^^^ '\r')
      }.withFailureMessage("expected valid string escape: one of \\\", \\t, \\n, \\f, or \\r")) |
        acceptMatch("string contents", { case c if c != '\"' => c })
    } ^^ { parts => parts.mkString("") }) <~ elem('\"')

  val tlaIdentifierExpr: Parser[TLAIdentifier] =
    withSourceLocation(tlaIdentifier) ^^ {
      case (loc, id) => new TLAIdentifier(loc, id)
    }

  val tlaStringExpr : Parser[TLAString] =
    withSourceLocation(tlaString) ^^ {
      case (loc, str) => new TLAString(loc, str)
    }

  val tlaNumberExpr: Parser[TLANumber] =
    withSourceLocation {
      regex(raw"\d+".r) ^^ ((_, TLANumber.Base.DECIMAL)) |
        regex(raw"\d*\.\d+".r) ^^ ((_, TLANumber.Base.DECIMAL)) |
        regex(raw"\\[bB][01]+".r) ^^ ((_, TLANumber.Base.BINARY)) |
        regex(raw"\\[oO][0-7]+".r) ^^ ((_, TLANumber.Base.OCTAL)) |
        regex(raw"\\[hH][0-9a-fA-F]+".r) ^^ ((_, TLANumber.Base.HEXADECIMAL))
    } ^^ {
      case (loc, (str, base)) => new TLANumber(loc, str, base)
    }

  def tlaCommaSep[T](p: =>Parser[T])(implicit ctx: TLAParserContext): Parser[List[T]] =
    repsep(p, wsChk ~> "," <~ wsChk)

  def tlaComma1Sep[T](p: =>Parser[T])(implicit ctx: TLAParserContext): Parser[List[T]] =
    rep1sep(p, wsChk ~> "," <~ wsChk)

  def tlaIdentifierOrTupleQuantifierBound(implicit ctx: TLAParserContext): Parser[TLAQuantifierBound] = {
    val idOrTuple: Parser[Either[List[TLAIdentifier],TLAIdentifier]] =
      "<<" ~> wsChk ~> tlaCommaSep(tlaIdentifierExpr) <~ wsChk <~ ">>" ^^ ((Left(_))) | tlaIdentifierExpr ^^ ((Right(_)))
    withSourceLocation(idOrTuple ~ (wsChk  ~> "\\in" ~> wsChk ~> tlaExpression)) ^^ {
      case (loc, Left(ids) ~ set) => new TLAQuantifierBound(loc, TLAQuantifierBound.Type.TUPLE, ids, set)
      case (loc, Right(id) ~ set) => new TLAQuantifierBound(loc, TLAQuantifierBound.Type.IDS, List(id), set)
    }
  }

  def tlaQuantifierBound(implicit ctx: TLAParserContext): Parser[TLAQuantifierBound] = {
    withSourceLocation(("<<" ~> wsChk ~> tlaCommaSep(tlaIdentifierExpr) <~ wsChk <~ ">>" <~ wsChk <~ "\\in") ~ (wsChk ~> tlaExpression)) ^^ {
      case (loc, ids ~ set) => new TLAQuantifierBound(loc, TLAQuantifierBound.Type.TUPLE, ids, set)
    } |
      withSourceLocation((tlaComma1Sep(tlaIdentifierExpr) <~ wsChk <~ "\\in") ~ (wsChk ~> tlaExpression)) ^^ {
        case (loc, ids ~ set) => new TLAQuantifierBound(loc, TLAQuantifierBound.Type.IDS, ids, set)
      }
  }

  def tlaInstancePrefix(implicit ctx: TLAParserContext): Parser[List[TLAGeneralIdentifierPart]] = {
    def impl(pfx: List[TLAGeneralIdentifierPart]): Parser[List[TLAGeneralIdentifierPart]] =
      withSourceLocation {
        withSourceLocation(tlaIdentifierExpr).flatMap {
          case (loc, id) =>
            ctx.lookupDefinition(pfx.map(_.getIdentifier) :+ id) match {
              case None =>
                failure(s"lookup failed for identifier ${pfx.map(_.getIdentifier).mkString("!")}!$id")
              case Some(defn) =>
                if(defn.arity == 0) {
                  wsChk ~> "!" ^^^ (id, Nil, defn)
                } else {
                  wsChk ~> "(" ~> wsChk ~> tlaComma1Sep(tlaExpression) <~ wsChk <~ ")" <~ wsChk <~ "!" ^^ ((id, _, defn))
                }
            }
        }
      }.flatMap {
        case (loc, (id, params, defn)) =>
          if(!defn.isModuleInstance) {
            throw KindMismatchError(loc)
          }
          if(params.length != defn.arity) {
            throw ArityMismatchError(loc, defn, params.length)
          }
          val part = new TLAGeneralIdentifierPart(loc, id, params.asJava)
          val path = pfx :+ part
          opt(wsChk ~> impl(path)) ^^ (_.getOrElse(path))
      }
    (impl(Nil) | success(Nil)).withFailureMessage("expected instance prefix")
  }

  def tlaTupleExpr(implicit ctx: TLAParserContext): Parser[TLATuple] =
    withSourceLocation {
      "<<" ~> wsChk ~> tlaCommaSep(tlaExpression) <~ wsChk <~ ">>"
    } ^^ {
      case (loc, exprs) => new TLATuple(loc, exprs.asJava)
    }

  def tlaRequiredActionExpr(implicit ctx: TLAParserContext): Parser[TLARequiredAction] =
    withSourceLocation {
      ("<<" ~> wsChk ~> tlaExpression <~ wsChk <~ ">>_") ~! (wsChk ~> tlaExpression)
    } ^^ {
      case (loc, body ~ vars) => new TLARequiredAction(loc, body, vars)
    }

  def tlaOperatorCallOrGeneralIdentifier(implicit ctx: TLAParserContext): Parser[TLAExpression] =
    withSourceLocation {
      withSourceLocation(tlaInstancePrefix ~ (wsChk ~> tlaIdentifierExpr)).flatMap {
        case (loc, pfx ~ id) =>
          ctx.lookupDefinition(pfx.map(_.getIdentifier) :+ id) match {
            case None =>
              ctx.lateBindingStack match {
                case lateBindings :: _ if pfx.isEmpty =>
                  // if the context allows late bindings (i.e names bound to the right)
                  // then assume arity == 0 and defer setRefersTo below
                  success((pfx, id, Right(lateBindings), Nil))
                case _ =>
                  throw DefinitionLookupError(loc, pfx, id)
              }
            case Some(defn) =>
              if( defn.arity > 0 ) {
                (wsChk ~> "(" ~> wsChk ~> repsep(tlaExpression, wsChk ~> "," <~ wsChk) <~ wsChk <~ ")") ^^
                  ((pfx, id, Left(defn), _))
              } else {
                success((pfx, id, Left(defn), Nil))
              }
          }
      }
    } ^^ {
      case (loc, (Nil, name, Right(lateBindings), Nil)) =>
        val ref = new TLAGeneralIdentifier(loc, name, Nil)
        lateBindings.getOrElseUpdate(name, mutable.ArrayBuffer.empty) += ref.setRefersTo
        ref
      case (loc, (pfx, name, Left(defn), params)) =>
        if( defn.arity != params.length) {
          throw ArityMismatchError(loc, defn, params.size)
        }
        if(params.isEmpty) {
          val ref = new TLAGeneralIdentifier(loc, name, pfx)
          ref.setRefersTo(defn)
          ref
        } else {
          val ref = new TLAOperatorCall(loc, name, pfx.asJava, params.asJava)
          ref.setRefersTo(defn)
          ref
        }
    }

  def tlaConjunctOrDisjunct(which: String)(implicit ctx: TLAParserContext): Parser[TLAExpression] = {
    val origCtx = ctx
    guard(withSourceLocation(which)).flatMap {
      case (loc, _) =>
        val lCtx = origCtx.withMinColumn(loc.getStartColumn)
        val rCtx = origCtx.withMinColumn(loc.getStartColumn + 1)
        implicit val ctx = rCtx
        rep1({
          implicit val ctx = lCtx
          wsChk ~> withSourceLocation(which)
        } ~ (wsChk ~> tlaExpression)) ^^ { parts =>
          val (_, resultExpr) = parts.tail.foldLeft((parts.head._1._1, parts.head._2)) { (acc, part) =>
            val (locationAcc, lhs) = acc
            val (symLoc, _) ~ rhs = part
            val combinedLoc = locationAcc.combine(rhs.getLocation)
            val sym = new TLASymbol(symLoc, which)
            val binop = new TLABinOp(combinedLoc, sym, Nil.asJava, lhs, rhs)
            // should always succeed, /\ and \/ are built-in
            binop.setRefersTo(ctx.lookupDefinition(List(sym.getIdentifier)).get)
            (combinedLoc, binop)
          }
          resultExpr
        }
    }
  }

  def tlaConjunctExpr(implicit ctx: TLAParserContext): Parser[TLAExpression] =
    tlaConjunctOrDisjunct("/\\")

  def tlaDisjunctExpr(implicit ctx: TLAParserContext): Parser[TLAExpression] =
    tlaConjunctOrDisjunct("\\/")

  def tlaIfExpr(implicit ctx: TLAParserContext): Parser[TLAIf] = {
    withSourceLocation {
      ("IF" ~>! wsChk ~> tlaExpression) ~ (wsChk ~> "THEN" ~>! wsChk ~> tlaExpression) ~
        (wsChk ~> "ELSE" ~>! wsChk ~> tlaExpression)
    } ^^ {
      case (loc, cond ~ yes ~ no) => new TLAIf(loc, cond, yes, no)
    }
  }

  def tlaCaseExpr(implicit ctx: TLAParserContext): Parser[TLACase] =
    withSourceLocation {
      ("CASE" ~>! wsChk ~> withSourceLocation(tlaExpression ~ (wsChk ~> "->" ~> wsChk ~> tlaExpression ))) ~
        (wsChk ~> repsep(withSourceLocation("[]" ~> wsChk ~> tlaExpression ~ (wsChk ~> "->" ~> wsChk ~> tlaExpression)), wsChk)) ~
        opt(wsChk ~> "[]" ~> wsChk ~> "OTHER" ~>! wsChk ~> "->" ~> wsChk ~> tlaExpression)
    } ^^ {
      case (loc, (loc1, cond1 ~ res1) ~ arms ~ other) =>
        new TLACase(
          loc,
          (new TLACaseArm(loc1, cond1, res1) :: arms.map { case (loc, cond ~ res) => new TLACaseArm(loc, cond, res) }).asJava,
          other.orNull)
    }

  def tlaFunctionExpr(implicit ctx: TLAParserContext): Parser[TLAFunction] = {
    val origCtx = ctx
    withSourceLocation {
      ("[" ~> wsChk ~> tlaComma1Sep(tlaQuantifierBound) <~ wsChk <~ "|->" <~! wsChk).flatMap { bounds =>
        implicit val ctx = bounds.foldLeft(origCtx)(_.withDefinition(_))
        (tlaExpression <~ wsChk <~ "]") ^^ ((bounds, _))
      }
    } ^^ {
      case (loc, (qbs, expr)) => new TLAFunction(loc, qbs.asJava, expr)
    }
  }

  def tlaRecordSetExpr(implicit ctx: TLAParserContext): Parser[TLARecordSet] =
    withSourceLocation {
      "[" ~> wsChk ~> tlaComma1Sep {
        withSourceLocation {
          tlaIdentifierExpr ~ (wsChk ~> ":" ~>! wsChk ~> tlaExpression)
        } ^^ { case (loc, name ~ set) => new TLARecordSet.Field(loc, name, set) }
      } <~ wsChk <~ "]"
    } ^^ {
      case (loc, fields) => new TLARecordSet(loc, fields.asJava)
    }

  def tlaRecordConstructorExpr(implicit ctx: TLAParserContext): Parser[TLARecordConstructor] =
    withSourceLocation {
      "[" ~> wsChk ~> tlaComma1Sep {
        withSourceLocation {
          tlaIdentifierExpr ~ (wsChk ~> "|->" ~>! wsChk ~> tlaExpression)
        } ^^ {
          case (loc, label ~ value) => new TLARecordConstructor.Field(loc, label, value)
        }
      } <~ wsChk <~ "]"
    } ^^ {
      case (loc, fields) => new TLARecordConstructor(loc, fields.asJava)
    }

  def tlaFunctionSetExpr(implicit ctx: TLAParserContext): Parser[TLAFunctionSet] =
    withSourceLocation {
      "[" ~> wsChk ~> tlaExpression ~ (wsChk ~> "->" ~>! wsChk ~> tlaExpression <~ wsChk <~ "]")
    } ^^ {
      case (loc, from ~ to) => new TLAFunctionSet(loc, from, to)
    }

  def tlaMaybeActionExpr(implicit ctx: TLAParserContext): Parser[TLAMaybeAction] =
    withSourceLocation {
      "[" ~> wsChk ~> tlaExpression ~ (wsChk ~> "]_" ~>! wsChk ~> tlaExpression)
    } ^^ {
      case (loc, body ~ vars) => new TLAMaybeAction(loc, body, vars)
    }

  def tlaFunctionSubstitutionExpr(implicit ctx: TLAParserContext): Parser[TLAFunctionSubstitution] =
    withSourceLocation {
      "[" ~> wsChk ~> tlaExpression ~ (wsChk ~> "EXCEPT" ~>! wsChk ~> tlaComma1Sep {
        withSourceLocation {
          "!" ~>! rep1 {
            wsChk ~> (
              withSourceLocation("." ~> wsChk ~> tlaIdentifierExpr) ^^ {
                case (loc, id) => new TLASubstitutionKey(loc, List(new TLAString(loc, id.getId): TLAExpression).asJava)
              } |
                withSourceLocation("[" ~> wsChk ~> tlaComma1Sep(tlaExpression) <~ wsChk <~ "]") ^^ {
                  case (loc, idxs) => new TLASubstitutionKey(loc, idxs.asJava)
                })
          } ~ (wsChk ~> "=" ~> wsChk ~> tlaExpression)
        } ^^ {
          case (loc, path ~ value) => new TLAFunctionSubstitutionPair(loc, path.asJava, value)
        }
      } <~ wsChk <~ "]")
    } ^^ {
      case (loc, fn ~ pairs) => new TLAFunctionSubstitution(loc, fn, pairs.asJava)
    }

  def tlaQuantifiedExistentialExpr(implicit ctx: TLAParserContext): Parser[TLAQuantifiedExistential] = {
    val origCtx = ctx
    withSourceLocation {
      ("\\E" ~> wsChk ~> tlaComma1Sep(tlaQuantifierBound)).flatMap(bounds => {
        implicit val ctx = bounds.foldLeft(origCtx)(_.withDefinition(_))
        (wsChk ~> ":" ~>! wsChk ~> tlaExpression) ^^ ((bounds, _))
      })
    } ^^ {
      case (loc, (bounds, predicate)) => new TLAQuantifiedExistential(loc, bounds.asJava, predicate)
    }
  }

  def tlaQuantifiedUniversalExpr(implicit ctx: TLAParserContext): Parser[TLAQuantifiedUniversal] = {
    val origCtx = ctx
    withSourceLocation {
      ("\\A" ~> wsChk ~> tlaComma1Sep(tlaQuantifierBound)).flatMap { bounds =>
        implicit val ctx = bounds.foldLeft(origCtx)(_.withDefinition(_))
        wsChk ~> ":" ~>! wsChk ~> tlaExpression ^^ ((bounds, _))
      }
    } ^^ {
      case (loc, (bounds, predicate)) => new TLAQuantifiedUniversal(loc, bounds.asJava, predicate)
    }
  }

  def tlaUnquantifiedExistentialExpr(implicit ctx: TLAParserContext): Parser[TLAExistential] = {
    val origCtx = ctx
    withSourceLocation {
      (("\\EE" | "\\E") ~> wsChk ~> tlaComma1Sep(tlaIdentifierExpr)).flatMap { ids =>
        implicit val ctx = ids.foldLeft(origCtx)(_.withDefinition(_))
        wsChk ~> ":" ~>! wsChk ~> tlaExpression ^^ ((ids, _))
      }
    } ^^ {
      case (loc, (ids, predicate)) => new TLAExistential(loc, ids.asJava, predicate)
    }
  }

  def tlaUnquantifiedUniversalExpr(implicit ctx: TLAParserContext): Parser[TLAUniversal] = {
    val origCtx = ctx
    withSourceLocation {
      (("\\AA" | "\\A") ~> wsChk ~> tlaComma1Sep(tlaIdentifierExpr)).flatMap { ids =>
        implicit val ctx = ids.foldLeft(origCtx)(_.withDefinition(_))
        wsChk ~> ":" ~>! wsChk ~> tlaExpression ^^ ((ids, _))
      }
    } ^^ {
      case (loc, (ids, predicate)) => new TLAUniversal(loc, ids.asJava, predicate)
    }
  }

  def tlaSetConstructorExpr(implicit ctx: TLAParserContext): Parser[TLASetConstructor] =
    withSourceLocation {
      "{" ~> wsChk ~> tlaCommaSep(tlaExpression) <~ wsChk <~ "}"
    } ^^ {
      case (loc, members) => new TLASetConstructor(loc, members.asJava)
    }

  def tlaSetRefinementExpr(implicit ctx: TLAParserContext): Parser[TLASetRefinement] =
    withSourceLocation {
      val origCtx = ctx
      ("{" ~> wsChk ~> tlaIdentifierOrTupleQuantifierBound <~ wsChk <~ ":").flatMap { binding =>
        implicit val ctx = origCtx.withDefinition(binding)
        (wsChk ~> tlaExpression <~ wsChk <~ "}") ^^ ((binding, _))
      }
    } ^^ {
      case (loc, (binding, whenExpr)) => new TLASetRefinement(loc, binding, whenExpr)
    }

  def tlaSetComprehensionExpr(implicit ctx: TLAParserContext): Parser[TLASetComprehension] = {
    val origCtx = ctx
    withSourceLocation {
      ("{" ~> wsChk ~> {
        implicit val ctx = origCtx.withLateBinding
        (tlaExpression <~ wsChk <~ ":") ^^ ((_, ctx.lateBindingStack.head))
      }) ~ (wsChk ~> tlaComma1Sep(tlaQuantifierBound) <~ wsChk <~ "}")
    } ^^ {
      case (loc, (expr, lateBindings) ~ bounds) =>
        // extract all late bindings from bounds, and match them up with any relevant elements
        // of lateBindings, removing them in the process
        def extractMembers(members: List[TLADefinition]): List[TLADefinitionOne] =
          members.flatMap {
            case defn: TLADefinitionOne => List(defn)
            case defn: TLADefinitionComposite => extractMembers(defn.members)
          }
        val defns: List[TLADefinitionOne] = bounds.flatMap(bind => extractMembers(bind.members))
        defns.foreach { defn =>
          lateBindings.get(defn.identifier) match {
            case Some(lateBind) =>
              lateBind.foreach(_(defn))
              lateBindings -= defn.identifier
            case None =>
          }
        }
        // if lateBindings is not empty after this (i.e we didn't match all the contained bindings)
        // then either these should be bound even later (add to the next late bindings map in the stack)
        // or we're out of possible late bindings, in which case raise an error indicating the location
        // of one of the remaining identifiers (alphabetically least, for consistency)
        if(lateBindings.nonEmpty) {
          ctx.lateBindingStack match {
            case Nil =>
              val id = lateBindings.keys.minBy(_.getId)
              throw DefinitionLookupError(id.getLocation, Nil, id)
            case outerBindings :: _ =>
              lateBindings.foreach {
                case (key, bindings) =>
                  outerBindings.getOrElseUpdate(key, mutable.ArrayBuffer.empty) ++= bindings
              }
              lateBindings.clear()
          }
        }
        new TLASetComprehension(loc, expr, bounds.asJava)
    }
  }

  def tlaLetExpr(implicit ctx: TLAParserContext): Parser[TLALet] =
    withSourceLocation {
      "LET" ~>! wsChk ~> {
        def impl(pfx: List[TLAUnit with TLADefinition])(implicit ctx: TLAParserContext): Parser[(List[TLAUnit with TLADefinition],TLAExpression)] = {
          val origCtx = ctx
          (tlaOperatorDefinition(isLocal=false) | tlaFunctionDefinition(isLocal=false) | tlaModuleDefinition(isLocal=false)).flatMap { (defn: TLAUnit with TLADefinition) =>
            implicit val ctx = origCtx.withDefinition(defn)
            val nextPfx = pfx :+ defn
            wsChk ~> (impl(nextPfx) | (("IN" ~>! wsChk ~> tlaExpression) ^^ ((nextPfx, _))))
          }
        }
        impl(Nil)
      }
    } ^^ {
      case (loc, (units, body)) => new TLALet(loc, units.map(u => u: TLAUnit).asJava, body)
    }

  def tlaFairnessConstraintExpr(implicit ctx: TLAParserContext): Parser[TLAFairness] =
    withSourceLocation {
      ("WF_" ^^^ TLAFairness.Type.WEAK | "SF_" ^^^ TLAFairness.Type.STRONG) ~!
        (wsChk ~> tlaExpression) ~!
        (wsChk ~> "(" ~> wsChk ~>! tlaExpression <~ wsChk <~ ")")
    } ^^ {
      case (loc, tpe ~ vars ~ expr) => new TLAFairness(loc, tpe, vars, expr)
    }

  val tlaPrefixOperator: Parser[String] =
    TLAMeta.prefixOperators.keys.toList.sorted.sortWith(_.length > _.length)
      .foldRight(failure("not a prefix operator"): Parser[String]) { (pfx, otherwise) =>
        if(pfx == "-_") { // special-case the syntactic anomaly that is "-"
          "-" ^^^ "-_" | otherwise
        } else {
          pfx | otherwise
        }
      }

  // same as tlaPrefixOperator, but will read -. instead of just -
  val tlaPrefixOperatorDef: Parser[String] =
    TLAMeta.prefixOperators.keys.toList.sorted.sortWith(_.length > _.length)
      .foldRight(failure("not a prefix operator"): Parser[String]) { (pfx, otherwise) =>
        if(pfx == "-_") { // special-case the syntactic anomaly that is "-"
          "-." ^^^ "-_" | otherwise
        } else {
          pfx | otherwise
        }
      }

  private lazy val tlaInfixOperatorV: Parser[String] =
    TLAMeta.infixOperators.keys.toList.sorted.sortWith(_.length > _.length)
      .foldRight(failure("not an infix operator"): Parser[String])(_ | _)
  def tlaInfixOperator: Parser[String] = tlaInfixOperatorV

  val tlaPostfixOperator: Parser[String] =
    TLAMeta.postfixOperators.keys.toList.sorted.sortWith(_.length > _.length)
      .foldRight(failure("not a postfix operator"): Parser[String])(_ | _)

  def tlaExpressionMinPrecedence(minPrecedence: Int)(implicit ctx: TLAParserContext): Parser[TLAExpression] = {
    val lhsWithPrefix = withSourceLocation(tlaInstancePrefix ~ (wsChk ~> withSourceLocation(tlaPrefixOperator))).flatMap {
      case (loc, pfx ~ ((symLoc, op))) =>
        val (lowPrec, highPrec) = TLAMeta.prefixOperators(op)
        wsChk ~> withSourceLocation(tlaExpressionMinPrecedence(highPrec + 1)) ^^ {
          case (loc2, innerExpr) =>
            val sym = new TLASymbol(symLoc, op)
            val result = new TLAUnary(loc.combine(loc2), sym, pfx.asJava, innerExpr)
            ctx.lookupDefinition(pfx.map(_.getIdentifier) :+ sym.getIdentifier) match {
              case None => throw DefinitionLookupError(loc, pfx, sym.getIdentifier)
              case Some(defn) => result.setRefersTo(defn)
            }
            result
        }
    } | tlaExpressionNoOperators

    def withPartOpt(lhsLoc: SourceLocation, lhs: TLAExpression, maxPrecedence: Int): Parser[TLAExpression] =
      withFunctionCall(lhsLoc, lhs, maxPrecedence) | withDot(lhsLoc, lhs, maxPrecedence) |
        withInfix(lhsLoc, lhs, maxPrecedence) | withPostfix(lhsLoc, lhs, maxPrecedence) |
        success(lhs)

    def withPostfix(lhsLoc: SourceLocation, lhs: TLAExpression, maxPrecedence: Int): Parser[TLAExpression] =
      withSourceLocation {
        (wsChk ~> tlaInstancePrefix) ~ (wsChk ~> withSourceLocation(tlaPostfixOperator)) ^? {
          case pfx ~ ((symLoc, op)) if TLAMeta.postfixOperators(op) >= minPrecedence =>
            (pfx, symLoc, op)
        }
      }.flatMap {
        case (loc, (pfx, symLoc, op)) =>
          val combinedLoc = lhsLoc.combine(loc)
          val sym = new TLASymbol(symLoc, op)
          val result = new TLAUnary(combinedLoc, sym, pfx.asJava, lhs)
          ctx.lookupDefinition(pfx.map(_.getIdentifier) :+ sym.getIdentifier) match {
            case None => throw DefinitionLookupError(loc, pfx, sym.getIdentifier)
            case Some(defn) => result.setRefersTo(defn)
          }
          withPartOpt(combinedLoc, result, maxPrecedence)
      }

    def withFunctionCall(lhsLoc: SourceLocation, lhs: TLAExpression, maxPrecedence: Int): Parser[TLAExpression] =
      if(minPrecedence <= 16) {
        withSourceLocation("[" ~> wsChk ~> tlaComma1Sep(tlaExpression) <~ wsChk <~ "]").flatMap {
          case (loc, args) =>
            val combinedLoc = lhsLoc.combine(loc)
            withPartOpt(combinedLoc, new TLAFunctionCall(combinedLoc, lhs, args.asJava), 15)
        }
      } else {
        failure("not at precedence 16")
      }

    def withDot(lhsLoc: SourceLocation, lhs: TLAExpression, maxPrecedence: Int): Parser[TLAExpression] =
      if(minPrecedence <= 17) {
        rep1sep(withSourceLocation("." ~> wsChk ~> tlaIdentifierExpr), wsChk).flatMap { dots =>
          val (combinedLoc, result) = dots.foldLeft((lhsLoc, lhs)) { (acc, dot) =>
            val (lhsLoc, lhs) = acc
            val (loc, id) = dot
            val combinedLoc = lhsLoc.combine(loc)
            (combinedLoc, new TLADot(combinedLoc, lhs, id.getId))
          }
          withPartOpt(combinedLoc, result, 16)
        }
      } else {
        failure("not at precedence 17")
      }

    def withInfix(lhsLoc: SourceLocation, lhs: TLAExpression, maxPrecedence: Int): Parser[TLAExpression] =
      withSourceLocation((wsChk ~> tlaInstancePrefix) ~ (wsChk ~> withSourceLocation(tlaInfixOperator)) ^? {
        case pfx ~ ((symLoc, op)) if TLAMeta.infixOperators(op)._1 >= minPrecedence && TLAMeta.infixOperators(op)._2 <= maxPrecedence =>
          (pfx, symLoc, op)
      }).flatMap {
        case (loc, (pfx, symLoc, op)) =>
          val (lowPrec, highPrec, leftAssoc) = TLAMeta.infixOperators(op)
          withSourceLocation(wsChk ~> tlaExpressionMinPrecedence(highPrec + 1)).flatMap {
            case (rhsLoc, rhs) =>
              val combinedLoc = lhsLoc.combine(loc.combine(rhsLoc))
              val sym = new TLASymbol(symLoc, op)
              val result = new TLABinOp(combinedLoc, sym, pfx.asJava, lhs, rhs)
              ctx.lookupDefinition(pfx.map(_.getIdentifier) :+ sym.getIdentifier) match {
                case None => throw DefinitionLookupError(loc, pfx, sym.getIdentifier)
                case Some(defn) => result.setRefersTo(defn)
              }
              if (leftAssoc) {
                def assoc(lhsLoc: SourceLocation, lhs: TLAExpression): Parser[TLAExpression] =
                  withSourceLocation {
                    (wsChk ~> tlaInstancePrefix) ~ (wsChk ~> withSourceLocation(op)) ~ (wsChk ~> tlaExpressionMinPrecedence(highPrec + 1))
                  }.flatMap {
                    case (loc, pfx ~ ((symLoc, _)) ~ rhs) =>
                      val combinedLoc = lhsLoc.combine(loc)
                      val sym = new TLASymbol(symLoc, op)
                      val nextLhs = new TLABinOp(combinedLoc, sym, pfx.asJava, lhs, rhs)
                      ctx.lookupDefinition(pfx.map(_.getIdentifier) :+ sym.getIdentifier) match {
                        case None => throw DefinitionLookupError(loc, pfx, sym.getIdentifier)
                        case Some(defn) => nextLhs.setRefersTo(defn)
                      }
                      assoc(combinedLoc, nextLhs) | withPartOpt(combinedLoc, nextLhs, lowPrec-1)
                  }
                assoc(combinedLoc, result) | withPartOpt(combinedLoc, result, lowPrec - 1)
              } else {
                withPartOpt(combinedLoc, result, lowPrec - 1)
              }
          }
      }

    withSourceLocation(lhsWithPrefix).flatMap { case (loc, lhs) => withPartOpt(loc, lhs, 18) }
  }

  def tlaExpressionNoOperators(implicit ctx: TLAParserContext): Parser[TLAExpression] =
    tlaNumberExpr |
      tlaStringExpr |
      withSourceLocation("TRUE" | "FALSE") ^^ { case (loc, str) => new TLABool(loc, str == "TRUE") } |
      ("(" ~>! wsChk ~> tlaExpression <~ wsChk <~ ")") |
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
      tlaSetRefinementExpr | tlaSetComprehensionExpr | tlaSetConstructorExpr

  def tlaExpression(implicit ctx: TLAParserContext): Parser[TLAExpression] =
    tlaExpressionMinPrecedence(0)

  def tlaOpDecl(implicit ctx: TLAParserContext): Parser[TLAOpDecl] = {
    val named =
      withSourceLocation {
        tlaIdentifierExpr ~ (wsChk ~> "(" ~> tlaComma1Sep("_") <~ wsChk <~ ")")
      } ^^ {
        case (loc, id ~ args) => TLAOpDecl.Named(loc, id, args.length)
      }
    val id = tlaIdentifierExpr ^^ { id => TLAOpDecl.Id(id.getLocation, id) }
    val prefix = withSourceLocation(withSourceLocation(tlaPrefixOperatorDef) <~ wsChk <~ "_") ^^ {
      case (loc, (opLoc, op)) => TLAOpDecl.Prefix(loc, new TLAIdentifier(opLoc, op))
    }
    val infix = withSourceLocation("_" ~> wsChk ~> withSourceLocation(tlaInfixOperator) <~ wsChk <~ "_") ^^ {
      case (loc, (opLoc, op)) => TLAOpDecl.Infix(loc, new TLAIdentifier(opLoc, op))
    }
    val postfix = withSourceLocation("_" ~> wsChk ~> withSourceLocation(tlaPostfixOperator)) ^^ {
      case (loc, (opLoc, op)) => TLAOpDecl.Postfix(loc, new TLAIdentifier(opLoc, op))
    }
    named | id | prefix | infix | postfix
  }

  def tlaOperatorDefinition(isLocal: Boolean)(implicit ctx: TLAParserContext): Parser[TLAOperatorDefinition] = {
    val origCtx = ctx
    val prefix = withSourceLocation {
      (withSourceLocation(tlaPrefixOperatorDef) ~ (wsChk ~> tlaIdentifierExpr)).flatMap {
        case (opLoc, op) ~ id =>
          implicit val ctx = origCtx.withDefinition(id)
          (wsChk ~> "==" ~> wsChk ~> tlaExpression) ^^ ((opLoc, op, id, _))
      }
    } ^^ {
      case (loc, (opLoc, op, id, body)) =>
        new TLAOperatorDefinition(
          loc, new TLAIdentifier(opLoc, op), List(TLAOpDecl.Id(id.getLocation, id)), body, isLocal)
    }
    val infix = withSourceLocation {
      (tlaIdentifierExpr ~ (wsChk ~> withSourceLocation(tlaInfixOperator)) ~ (wsChk ~> tlaIdentifierExpr)).flatMap {
        case lhsId ~ ((opLoc, op)) ~ rhsId =>
          implicit val ctx = origCtx.withDefinition(lhsId).withDefinition(rhsId)
          (wsChk ~> "==" ~> wsChk ~> tlaExpression) ^^ ((lhsId, opLoc, op, rhsId, _))
      }
    } ^^ {
      case (loc, (lhsId, opLoc, op, rhsId, body)) =>
        new TLAOperatorDefinition(
          loc, new TLAIdentifier(opLoc, op), List(
            TLAOpDecl.Id(lhsId.getLocation, lhsId), TLAOpDecl.Id(rhsId.getLocation, rhsId)),
          body, isLocal)
    }
    val postfix = withSourceLocation {
      (tlaIdentifierExpr ~ (wsChk ~> withSourceLocation(tlaPostfixOperator))).flatMap {
        case id ~ ((opLoc, op)) =>
          implicit val ctx = origCtx.withDefinition(id)
          (wsChk ~> "==" ~> wsChk ~> tlaExpression) ^^ ((id, opLoc, op, _))
      }
    } ^^ {
      case (loc, (id, opLoc, op, body)) =>
        new TLAOperatorDefinition(
          loc, new TLAIdentifier(opLoc, op), List(TLAOpDecl.Id(id.getLocation, id)), body, isLocal)
    }
    val nonfix = withSourceLocation {
      (tlaIdentifierExpr ~ opt(wsChk ~> "(" ~> tlaComma1Sep(tlaOpDecl) <~ wsChk <~ ")") <~ wsChk <~ "==" <~ wsChk).flatMap {
        case id ~ None => tlaExpression ^^ ((id, Nil, _))
        case id ~ Some(opDecls) =>
          implicit val ctx = opDecls.foldLeft(origCtx)(_.withDefinition(_))
          tlaExpression ^^ ((id, opDecls, _))
      }
    } ^^ {
      case (loc, (id, opDecls, body)) => new TLAOperatorDefinition(loc, id, opDecls, body, isLocal)
    }

    prefix | infix | postfix | nonfix
  }

  def tlaFunctionDefinition(isLocal: Boolean)(implicit ctx: TLAParserContext): Parser[TLAFunctionDefinition] = {
    val origCtx = ctx
    withSourceLocation {
      (tlaIdentifierExpr ~ (wsChk ~> "[" ~> wsChk ~> tlaComma1Sep(tlaQuantifierBound) <~ wsChk <~ "]" <~ wsChk <~ "==")).flatMap {
        case id ~ bounds =>
          implicit val ctx = bounds.foldLeft(origCtx)(_.withDefinition(_))
          (wsChk ~> tlaExpression) ^^ ((id, bounds, _))
      }
    } ^^ {
      case (loc, (id, bounds, body)) =>
        new TLAFunctionDefinition(loc, id, new TLAFunction(loc, bounds.asJava, body), isLocal)
    }
  }

  def tlaInstance(isLocal: Boolean)(implicit ctx: TLAParserContext): Parser[TLAInstance] =
    withSourceLocation {
      "INSTANCE" ~> wsChk ~> tlaIdentifierExpr ~
        opt(wsChk ~> "WITH" ~> tlaComma1Sep(
          withSourceLocation(withSourceLocation(tlaIdentifier | tlaPrefixOperatorDef | tlaInfixOperator | tlaPostfixOperator) ~
            (wsChk ~> "<-" ~> wsChk ~> tlaExpression))))
    } ^^ {
      case (loc, moduleId ~ substitutionsOpt) =>
        val substitutions = substitutionsOpt.getOrElse(Nil).map {
          case (loc, (idLoc, id) ~ expr) =>
            new TLAInstance.Remapping(loc, new TLAIdentifier(idLoc, id), expr)
        }
        // TODO: load the module data
        new TLAInstance(loc, moduleId, substitutions, isLocal)
    }

  def tlaModuleDefinition(isLocal: Boolean)(implicit ctx: TLAParserContext): Parser[TLAModuleDefinition] = {
    withSourceLocation {
      val origCtx = ctx
      (tlaIdentifierExpr ~ opt(wsChk ~> "(" ~> tlaComma1Sep(tlaOpDecl) <~ wsChk <~ ")")).flatMap {
        case id ~ argsOpt =>
          implicit val ctx = argsOpt.getOrElse(Nil).foldLeft(origCtx)(_.withDefinition(_))
          (wsChk ~> "==" ~> wsChk ~> tlaInstance(isLocal)) ^^ ((id, argsOpt.getOrElse(Nil), _))
      }
    } ^^ {
      case (loc, (id, args, instance)) => new TLAModuleDefinition(loc, id, args, instance, isLocal)
    }
  }

  def tlaModule(implicit ctx: TLAParserContext): Parser[TLAModule] =
    withSourceLocation {
      val origCtx = ctx
      ("----" ~> rep(elem('-')) ~> wsChk ~> "MODULE" ~>! wsChk ~> tlaIdentifierExpr <~ wsChk <~ "----" <~ rep(elem('-')) <~ wsChk) ~
        opt("EXTENDS" ~>! wsChk ~> tlaComma1Sep(tlaIdentifierExpr) <~ wsChk).flatMap { exts =>
          def unitRec(implicit ctx: TLAParserContext): Parser[List[TLAUnit]] = {
            val origCtx = ctx
            opt("----" ~> rep(elem('-')) ~> wsChk) ~> tlaUnit.flatMap { unit =>
              implicit val ctx = unit.definitions.foldLeft(origCtx)(_.withDefinition(_))
              (wsChk ~> unitRec ^^ (unit :: _)) | success(List(unit))
            }
          }
          val extensions = exts.getOrElse(Nil).map(origCtx.lookupModuleExtends)
          implicit val ctx = extensions.foldLeft(origCtx) { (ctx, ext) => ext.members.foldLeft(ctx)(_.withDefinition(_)) }
          (unitRec | success(Nil)) ^^ ((extensions, _))
        } <~ wsChk <~ "====" <~ rep(elem('='))
    } ^^ {
      case (loc, name ~ ((exts, units))) => new TLAModule(loc, name, exts, units)
    }

  def tlaUnit(implicit ctx: TLAParserContext): Parser[TLAUnit] = {
    val variableDeclaration = withSourceLocation {
      ("VARIABLES" | "VARIABLE") ~>! wsChk ~> tlaComma1Sep(tlaIdentifierExpr)
    } ^^ { case (loc, vars) => new TLAVariableDeclaration(loc, vars) }
    val constantDeclaration = withSourceLocation {
      ("CONSTANTS" | "CONSTANT") ~>! wsChk ~> tlaComma1Sep(tlaOpDecl)
    } ^^ { case (loc, decls) => new TLAConstantDeclaration(loc, decls) }
    val assumption = withSourceLocation {
      ("ASSUME" | "ASSUMPTION" | "AXIOM") ~>! wsChk ~> tlaExpression
    } ^^ { case (loc, expr) => new TLAAssumption(loc, expr) }
    val theorem = withSourceLocation {
      "THEOREM" ~>! wsChk ~> tlaExpression
    } ^^ { case (loc, expr) => new TLATheorem(loc, expr) }

    ("LOCAL" ~>! wsChk ~> {
        tlaInstance(true) | tlaModuleDefinition(true) | tlaFunctionDefinition(true) |
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
      tlaModule
  }

  val findTLAModule: Parser[Unit] =
    rep(not("----") ~> accept("anything", { case _ => () })) ^^^ ()

  def tlaModuleBeforeTranslation(implicit ctx: TLAParserContext): Parser[TLAModule] =
    withSourceLocation {
      val translationTag = "\\*" <~ rep("*") <~ rep(" ") <~ "BEGIN" <~ rep(" ") <~ "TRANSLATION"
      val wsWithoutTranslationTag =
        rep(regex("""\s+""".r) | tlaMultilineComment | not(translationTag) ~> tlaLineComment)

      val origCtx = ctx
      ("----" ~> rep(elem('-')) ~> wsChk ~> "MODULE" ~>! wsChk ~> tlaIdentifierExpr <~ wsChk <~ "----" <~ rep(elem('-'))) ~
        opt(wsChk ~> "EXTENDS" ~>! wsChk ~> tlaComma1Sep(tlaIdentifierExpr) <~ wsWithoutTranslationTag).flatMap { exts =>
          def unitRec(implicit ctx: TLAParserContext): Parser[List[TLAUnit]] = {
            val origCtx = ctx
            opt("----" ~> rep(elem('-')) ~> wsWithoutTranslationTag) ~> tlaUnit.flatMap { unit =>
              implicit val ctx = unit.definitions.foldLeft(origCtx)(_.withDefinition(_))
              (wsWithoutTranslationTag ~> unitRec ^^ (unit :: _)) | success(List(unit))
            }
          }
          val extensions = exts.getOrElse(Nil).map(origCtx.lookupModuleExtends)
          implicit val ctx = extensions.foldLeft(origCtx) { (ctx, ext) => ext.members.foldLeft(ctx)(_.withDefinition(_)) }
          (unitRec | success(Nil)) ^^ ((extensions, _))
        } <~ wsWithoutTranslationTag <~ translationTag
    } ^^ {
      case (loc, name ~ ((exts, units))) => new TLAModule(loc, name, exts, units)
    }
}

object TLAParser extends TLAParser with ParsingUtils {
  def readExpression(path: java.nio.file.Path, seq: CharSequence): TLAExpression = {
    implicit val ctx = TLABuiltinModules.Intrinsics.members.foldLeft(TLAParserContext())(_.withDefinition(_))
    checkResult {
      phrase(wsChk ~> tlaExpression <~ wsChk)(buildReader(path, seq))
    }
  }

  def readModule(path: java.nio.file.Path, seq: CharSequence): TLAModule = {
    implicit val ctx = TLABuiltinModules.Intrinsics.members.foldLeft(TLAParserContext())(_.withDefinition(_))
    checkResult(phrase(
      findTLAModule ~> tlaModule <~ rep(accept("anything", { case _ => () })))(buildReader(path, seq)))
  }

  def readModuleBeforeTranslation(path: java.nio.file.Path, seq: CharSequence): TLAModule = {
    implicit val ctx = TLABuiltinModules.Intrinsics.members.foldLeft(TLAParserContext())(_.withDefinition(_))
    checkResult(phrase(
      findTLAModule ~> tlaModuleBeforeTranslation <~ rep(accept("anything", { case _ => () })))(buildReader(path, seq)))
  }
}
