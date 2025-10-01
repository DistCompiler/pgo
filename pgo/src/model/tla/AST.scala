package pgo.model.tla

import pgo.model.{
  Definition,
  DefinitionComposite,
  DefinitionOne,
  RefersTo,
  Rewritable,
  SourceLocatable,
}

import scala.collection.View
import pgo.parser.TLAParserContext
import pgo.parser.ModuleNotFoundError
import pgo.model.SourceLocation
import pgo.model.SourceLocationWithUnderlying
import pgo.model.Visitable

sealed abstract class TLANode extends Rewritable with SourceLocatable {
  override def decorateLike(succ: this.type): this.type =
    super.decorateLike(succ.setSourceLocation(sourceLocation))

  def guessPath: Option[os.Path] =
    sourceLocation match
      case loc: SourceLocationWithUnderlying =>
        loc.underlying match
          case file: SourceLocation.UnderlyingFile =>
            Some(file.path / os.up)
          case _ => None
      case _ => None
  end guessPath
}

final case class TLASymbol(symbol: TLASymbol.Symbol) extends TLANode

object TLASymbol {
  private class Instances[T](val array: IArray[T]) extends AnyVal

  private inline given summonInstances[T: reflect.ClassTag](using
      mirror: deriving.Mirror.SumOf[T],
  ): Instances[T] =
    given [S <: Singleton](using v: ValueOf[S]): S = v.value
    Instances:
      compiletime
        .summonAll[mirror.MirroredElemTypes]
        .toIArray
        .map(_.asInstanceOf[T])

  private lazy val symbolMap: Map[String, Symbol] = {
    summon[Instances[Symbol]].array.iterator
      .flatMap(sym => sym.representations.view.map(_ -> sym))
      .toMap
  }

  def forString(symStr: String): Symbol = {
    require(
      symbolMap.contains(symStr),
      s"""could not find a Symbol instance for "$symStr"""",
    )
    symbolMap(symStr)
  }

  sealed abstract class Symbol(val representations: String*) {
    self: Singleton & Product =>
    override def toString: String = s"Symbol(${representations.mkString(", ")})"

    import pgo.parser.TLAMeta

    assert(
      representations.forall { rep =>
        TLAMeta.prefixOperators.contains(rep) ||
        TLAMeta.infixOperators.contains(rep) ||
        TLAMeta.postfixOperators.contains(rep)
      },
      s"this symbol does not have parser metadata: $this; this is almost 100% an implementation typo",
    )
    assert(
      isPrefix ^ isInfix ^ isPostfix,
      s"$this has more than one fixity; this is almost 100% an implementation typo",
    )

    def isPrefix: Boolean =
      TLAMeta.prefixOperators.contains(representations.head)

    def isInfix: Boolean =
      TLAMeta.infixOperators.contains(representations.head)

    def isPostfix: Boolean =
      TLAMeta.postfixOperators.contains(representations.head)

    def isAssociative: Boolean =
      TLAMeta.infixOperators.get(representations.head).exists(_._3)

    def precedence: Int = {
      require(precedenceLow == precedenceHigh)
      precedenceLow
    }

    /** A canonical string to represent this symbol at definition site
      */
    def stringReprDefn: String = representations.head

    /** A canonical string to represent this symbol when referenced in an
      * expression
      */
    def stringReprUsage: String = representations.head

    def productPrefix: String

    def precedenceLow: Int =
      TLAMeta.prefixOperators
        .get(representations.head)
        .map(_._1)
        .orElse(TLAMeta.infixOperators.get(representations.head).map(_._1))
        .orElse(TLAMeta.postfixOperators.get(representations.head))
        .get

    def precedenceHigh: Int =
      TLAMeta.prefixOperators
        .get(representations.head)
        .map(_._2)
        .orElse(TLAMeta.infixOperators.get(representations.head).map(_._2))
        .orElse(TLAMeta.postfixOperators.get(representations.head))
        .get
  }

  // prefix
  case object UnchangedSymbol extends Symbol("UNCHANGED")
  case object EnabledSymbol extends Symbol("ENABLED")
  case object DomainSymbol extends Symbol("DOMAIN")
  case object PrefixSubsetSymbol extends Symbol("SUBSET")
  case object LogicalNotSymbol extends Symbol("~", "\\lnot", "\\neg")
  case object PrefixUnionSymbol extends Symbol("UNION")
  case object TLEventuallySymbol extends Symbol("<>")
  case object TLAlwaysSymbol extends Symbol("[]")
  case object NegationSymbol extends Symbol("-_") {
    override def stringReprUsage: String = "-"
  }

  // infix
  case object DoubleExclamationSymbol extends Symbol("!!")
  case object NotEqualsSymbol extends Symbol("#", "/=")
  case object DoublePoundSymbol extends Symbol("##")
  case object DollarSymbol extends Symbol("$")
  case object DoubleDollarSymbol extends Symbol("$$")
  case object PercentSymbol extends Symbol("%")
  case object DoublePercentSymbol extends Symbol("%%")
  case object AmpersandSymbol extends Symbol("&")
  case object DoubleAmpersandSymbol extends Symbol("&&")
  case object OPlusSymbol extends Symbol("(+)", "\\oplus")
  case object OMinusSymbol extends Symbol("(-)", "\\ominus")
  case object ODotSymbol extends Symbol("(.)", "\\odot")
  case object OSlashSymbol extends Symbol("(/)", "\\oslash")
  case object OTimesSymbol extends Symbol("(\\X)", "\\otimes")
  case object AsteriskSymbol extends Symbol("*")
  case object DoubleAsteriskSymbol extends Symbol("**")
  case object PlusSymbol extends Symbol("+")
  case object DoublePlusSymbol extends Symbol("++")
  case object MinusSymbol extends Symbol("-")
  case object PlusArrowSymbol extends Symbol("-+->")
  case object DoubleMinusSymbol extends Symbol("--")
  case object LeftTurnstileSymbol extends Symbol("-|")
  case object DotSymbol extends Symbol(".") // TODO: this isn't reachable is it?
  case object DotDotSymbol extends Symbol("..")
  case object DotDotDotSymbol extends Symbol("...")
  case object SlashSymbol extends Symbol("/")
  case object SlashSlashSymbol extends Symbol("//")
  case object LogicalAndSymbol extends Symbol("/\\", "\\land")
  case object ColonColonEqualsSymbol extends Symbol("::=")
  case object ColonEqualsSymbol extends Symbol(":=")
  case object ColonGreaterThanSymbol extends Symbol(":>")
  case object LessThanSymbol extends Symbol("<")
  case object LessThanColonSymbol extends Symbol("<:")
  case object LessThanOrEqualSymbol extends Symbol("<=", "\\leq", "=<")
  case object EquivSymbol extends Symbol("<=>", "\\equiv")
  case object EqualsSymbol extends Symbol("=")
  case object ImpliesSymbol extends Symbol("=>")
  case object LeftEntailmentSymbol extends Symbol("=|")
  case object GreaterThanSymbol extends Symbol(">")
  case object GreaterThanOrEqualSymbol extends Symbol(">=", "\\geq")
  case object QuestionMarkSymbol extends Symbol("?")
  case object DoubleQuestionMarkSymbol extends Symbol("??")
  case object DoubleAtSignSymbol extends Symbol("@@")
  case object BackslashSymbol extends Symbol("\\")
  case object LogicalOrSymbol extends Symbol("\\/", "\\lor")
  case object ApproxSymbol extends Symbol("\\approx")
  case object AsympSymbol extends Symbol("\\asymp")
  case object BigCircSymbol extends Symbol("\\bigcirc")
  case object BulletSymbol extends Symbol("\\bullet")
  case object IntersectSymbol extends Symbol("\\intersect", "\\cap")
  case object CDotSymbol extends Symbol("\\cdot")
  case object OSymbol extends Symbol("\\o", "\\circ")
  case object CongruenceSymbol extends Symbol("\\cong")
  case object UnionSymbol extends Symbol("\\union", "\\cup")
  case object DivSymbol extends Symbol("\\div")
  case object DotEqSymbol extends Symbol("\\doteq")
  case object GreaterThanGreaterThanSymbol extends Symbol("\\gg")
  case object InSymbol extends Symbol("\\in")
  case object LessThanLessThanSymbol extends Symbol("\\ll")
  case object NotInSymbol extends Symbol("\\notin")
  case object PrecSymbol extends Symbol("\\prec")
  case object PrecEqSymbol extends Symbol("\\preceq")
  case object ProptoSymbol extends Symbol("\\propto")
  case object SimSymbol extends Symbol("\\sim")
  case object SquareCapSymbol extends Symbol("\\sqcap")
  case object SquareCupSymbol extends Symbol("\\sqcup")
  case object SquareSubsetSymbol extends Symbol("\\sqsubset")
  case object SquareSubsetOrEqualSymbol extends Symbol("\\sqsubseteq")
  case object SquareSupersetSymbol extends Symbol("\\sqsupset")
  case object SquareSupersetOrEqualSymbol extends Symbol("\\sqsupseteq")
  case object StarSymbol extends Symbol("\\star")
  case object SubsetSymbol extends Symbol("\\subset")
  case object SubsetOrEqualSymbol extends Symbol("\\subseteq")
  case object SuccSymbol extends Symbol("\\succ")
  case object SuccOrEqualSymbol extends Symbol("\\succeq")
  case object SupersetSymbol extends Symbol("\\supset")
  case object SupersetOrEqualSymbol extends Symbol("\\supseteq")
  case object UPlusSymbol extends Symbol("\\uplus")
  case object WRSymbol extends Symbol("\\wr")
  case object SuperscriptSymbol extends Symbol("^")
  case object CaretCaretSymbol extends Symbol("^^")
  case object PipeSymbol extends Symbol("|")
  case object TurnstileSymbol extends Symbol("|-")
  case object EntailmentSymbol extends Symbol("|=")
  case object DoublePipeSymbol extends Symbol("||")
  case object SequencingSymbol extends Symbol("~>")

  // postfix
  case object SuperscriptPlusSymbol extends Symbol("^+")
  case object SuperscriptAsteriskSymbol extends Symbol("^*")
  case object SuperscriptPoundSymbol extends Symbol("^#")
  case object PrimeSymbol extends Symbol("'")

}

final case class TLAIdentifier(id: String) extends TLANode {
  lazy val toDefiningIdentifier: TLADefiningIdentifier =
    TLADefiningIdentifier(this).setSourceLocation(sourceLocation)
}

final case class TLADefiningIdentifier(id: TLAIdentifier)
    extends TLANode
    with DefinitionOne {
  override def arity: Int = 0
  override def identifier: Definition.ScopeIdentifier =
    Definition.ScopeIdentifierName(id)
}

final case class TLAGeneralIdentifierPart(
    id: TLAIdentifier,
    parameters: List[TLAExpression],
) extends TLANode

final case class TLAQuantifierBound(
    tpe: TLAQuantifierBound.Type,
    ids: List[TLADefiningIdentifier],
    set: TLAExpression,
) extends TLANode
    with DefinitionComposite {
  // TODO: this is provably false from the grammar. Why did I assert this?
  // require(
  //   tpe match {
  //     case TLAQuantifierBound.IdsType   => ids.length == 1
  //     case TLAQuantifierBound.TupleType => true
  //   },
  //   s"a TLA+ QuantifierBound can restrict either a single identifier or a tuple, not multiple identifiers",
  // )

  override def definitions: View[Definition] = ids.view
}

object TLAQuantifierBound {
  sealed abstract class Type
  case object IdsType extends Type
  case object TupleType extends Type
}

final case class TLAOpDecl(variant: TLAOpDecl.Variant)
    extends TLANode
    with DefinitionOne {
  override def arity: Int = variant.arity
  override def identifier: Definition.ScopeIdentifier = variant.identifier
}

object TLAOpDecl {
  sealed abstract class Variant {
    def identifier: Definition.ScopeIdentifier
    def arity: Int
  }

  final case class NamedVariant(ident: TLAIdentifier, arity: Int)
      extends Variant {
    override def identifier: Definition.ScopeIdentifier =
      Definition.ScopeIdentifierName(ident)
  }

  final case class SymbolVariant(sym: TLASymbol) extends Variant {
    override def arity: Int =
      if (sym.symbol.isPrefix || sym.symbol.isPostfix) 1 else 2
    override def identifier: Definition.ScopeIdentifier =
      Definition.ScopeIdentifierSymbol(sym)
  }
}

sealed abstract class TLAUnit extends TLANode {
  def definitions: View[Definition]
}

final case class TLAAssumption(assumption: TLAExpression) extends TLAUnit {
  override def definitions: View[Definition] = View.empty
}

final case class TLAConstantDeclaration(constants: List[TLAOpDecl])
    extends TLAUnit
    with DefinitionComposite {
  override def definitions: View[Definition] = constants.view
}

final case class TLAInstance(
    moduleName: TLAIdentifier,
    remappings: List[TLAInstanceRemapping],
    isLocal: Boolean,
) extends TLAUnit
    with DefinitionComposite {
  override def definitions: View[Definition] =
    TLAParserContext.findModule(
      Definition.ScopeIdentifierName(moduleName),
      pwdOpt = guessPath,
    ) match
      case None =>
        throw ModuleNotFoundError(Definition.ScopeIdentifierName(moduleName))
      case Some(tlaModule) =>
        tlaModule.moduleDefinitions(captureLocal = false)
}

final case class TLAInstanceRemapping(
    from: Definition.ScopeIdentifier,
    to: TLAExpression,
) extends TLANode
    with DefinitionOne {
  override def arity: Int = 0
  override def identifier: Definition.ScopeIdentifier = from
}

final case class TLAModule(
    name: TLAIdentifier,
    exts: List[TLAIdentifier],
    units: List[TLAUnit],
) extends TLAUnit
    with DefinitionOne {
  override def definitions: View[Definition] = View(this)
  override def arity: Int = 0
  override def identifier: Definition.ScopeIdentifierName =
    Definition.ScopeIdentifierName(name)

  // override namedParts: our nameParts might be nested _within_ a unit, rather than the unit itself (e.g anything with opdecls)
  override def namedParts: Iterator[RefersTo.HasReferences] =
    units.iterator.flatMap(
      _.definitions.map(_.asInstanceOf[RefersTo.HasReferences]),
    )

  def moduleDefinitions(
      captureLocal: Boolean = false,
  ): View[DefinitionOne] =
    exts.view.flatMap: ext =>
      TLAParserContext.findModule(
        Definition.ScopeIdentifierName(ext),
        guessPath,
      ) match
        case None =>
          throw ModuleNotFoundError(Definition.ScopeIdentifierName(ext))
        case Some(module) =>
          module.moduleDefinitions(captureLocal = false)
    ++ units.view
      .flatMap(_.definitions)
      .flatMap(_.singleDefinitions)
      .filter(defn => if captureLocal then true else !defn.isLocal)
  end moduleDefinitions

  override def mapChildren(fn: Any => Any): this.type = {
    val mapped = super.mapChildren(fn)
    assert(
      mapped.exts eq exts,
      s"internal error: can't automatically rewrite module contents after replacing EXTENDS clause(s)",
    )
    mapped.asInstanceOf
  }

  def dependencies: List[TLAModule] =
    val modView = exts.view
      .flatMap: ext =>
        TLAParserContext.findModule(
          Definition.ScopeIdentifierName(ext),
          guessPath,
        )
    ++ units.view
      .flatMap: unit =>
        val mods = List.newBuilder[TLAModule]
        unit.visit(Visitable.BottomUpFirstStrategy):
          case inst: TLAInstance =>
            mods ++= TLAParserContext.findModule(
              Definition.ScopeIdentifierName(inst.moduleName),
            )
        mods.result()
    end modView

    modView.iterator.distinct.toList
  end dependencies
}

final case class TLAModuleDefinition(
    name: TLAIdentifier,
    args: List[TLAOpDecl],
    instance: TLAInstance,
    override val isLocal: Boolean,
) extends TLAUnit
    with DefinitionOne {
  lazy val localScope: Map[String, DefinitionOne] =
    TLAParserContext.findModule(
      Definition.ScopeIdentifierName(instance.moduleName),
      pwdOpt = guessPath,
    ) match
      case None =>
        throw ModuleNotFoundError(
          Definition.ScopeIdentifierName(instance.moduleName),
        )
      case Some(module) =>
        module
          .moduleDefinitions(captureLocal = false)
          .map: defn =>
            defn.canonicalIdString -> defn
          .toMap
  def definitions: View[Definition] = View(this)
  // override def definitions: View[Definition] =
  //   TLAParserContext.findModule(
  //     Definition.ScopeIdentifierName(instance.moduleName),
  //     pwdOpt = guessPath,
  //   ) match
  //     case None =>
  //       throw ModuleNotFoundError(
  //         Definition.ScopeIdentifierName(instance.moduleName),
  //       )
  //     case Some(module) =>
  //       module
  //         .moduleDefinitions(captureLocal = false, qualified = false)
  //         .map(
  //           QualifiedDefinition(Definition.ScopeIdentifierName(name), _, this),
  //         )
  override def arity: Int = args.size
  override def isModuleInstance: Boolean = true
  override def identifier: Definition.ScopeIdentifier =
    Definition.ScopeIdentifierName(name)
}

final case class TLAOperatorDefinition(
    name: Definition.ScopeIdentifier,
    args: List[TLAOpDecl],
    body: TLAExpression,
    override val isLocal: Boolean,
) extends TLAUnit
    with DefinitionOne {
  require(
    name match {
      case Definition.ScopeIdentifierSymbol(TLASymbol(sym)) =>
        if (sym.isPrefix || sym.isPostfix) args.length == 1
        else args.length == 2
      case Definition.ScopeIdentifierName(_) => true
    },
    s"symbolic operator definitions ($this) must exactly one or two arguments, depending on the symbol's fixity",
  )

  override def definitions: View[Definition] = View(this)

  override def arity: Int = args.length

  override def identifier: Definition.ScopeIdentifier = name
}

final case class TLATheorem(theorem: TLAExpression) extends TLAUnit {
  override def definitions: View[Definition] = View.empty
}

final case class TLAVariableDeclaration(variables: List[TLADefiningIdentifier])
    extends TLAUnit
    with DefinitionComposite {
  override def definitions: View[Definition] = variables.view
}

final case class TLARecursive(decls: List[TLARecursive.Decl]) extends TLAUnit {
  override def definitions: View[Definition] = decls.view
}

object TLARecursive {
  final case class Decl(decl: TLAOpDecl)
      extends TLANode
      with DefinitionOne
      with RefersTo[TLAOperatorDefinition] {
    override def arity: Int = decl.arity
    override def identifier: Definition.ScopeIdentifier = decl.identifier
  }
}

sealed abstract class TLAExpression extends TLANode

final case class TLAExtensionExpression(contents: Any) extends TLAExpression

final case class TLAString(value: String) extends TLAExpression

final case class TLANumber(
    value: TLANumber.Value,
    syntax: TLANumber.Syntax = TLANumber.DecimalSyntax,
) extends TLAExpression

object TLANumber {
  sealed abstract class Value
  final case class IntValue(value: BigInt) extends Value
  final case class DecimalValue(value: BigDecimal) extends Value

  sealed abstract class Syntax
  case object DecimalSyntax extends Syntax
  case object BinarySyntax extends Syntax
  case object OctalSyntax extends Syntax
  case object HexadecimalSyntax extends Syntax
}

final case class TLAGeneralIdentifier(
    name: TLAIdentifier,
    prefix: List[TLAGeneralIdentifierPart],
) extends TLAExpression
    with RefersTo[DefinitionOne] {
  override def setRefersTo(
      refersTo: DefinitionOne,
  ): TLAGeneralIdentifier.this.type = {
    // TODO: why is this sometimes not true, but things seem fine?
    // assert(refersTo.identifier.isInstanceOf[ScopeIdentifierName] && name == refersTo.identifier.asInstanceOf[ScopeIdentifierName].name,
    //   s"it is probably a bug that an identifier with lexical name $name actually refers to ${refersTo.identifier}")
    super.setRefersTo(refersTo)
  }
}

final case class TLADot(lhs: TLAExpression, identifier: TLAIdentifier)
    extends TLAExpression

final case class TLACrossProduct(operands: List[TLAExpression])
    extends TLAExpression {
  require(
    operands.size >= 2,
    "it makes no sense to construct a cross product of fewer than 2 elements",
  )
}

final case class TLAOperatorCall(
    name: Definition.ScopeIdentifier,
    prefix: List[TLAGeneralIdentifierPart],
    arguments: List[TLAExpression],
) extends TLAExpression
    with RefersTo[DefinitionOne] {
  override def setRefersTo(
      refersTo: DefinitionOne,
  ): TLAOperatorCall.this.type = {
    // TODO: why is this sometimes not true, but things seem fine?
    // assert(refersTo.identifier == name, s"it is probably a bug that an operator call with lexical name $name actually refers to ${refersTo.identifier}")
    super.setRefersTo(refersTo)
  }
}

final case class TLAIf(
    cond: TLAExpression,
    tval: TLAExpression,
    fval: TLAExpression,
) extends TLAExpression

final case class TLALet(defs: List[TLAUnit], body: TLAExpression)
    extends TLAExpression

final case class TLACase(arms: List[TLACaseArm], other: Option[TLAExpression])
    extends TLAExpression {
  require(arms.nonEmpty)
}

final case class TLACaseArm(cond: TLAExpression, result: TLAExpression)
    extends TLANode

final case class TLAMaybeAction(body: TLAExpression, vars: TLAExpression)
    extends TLAExpression

final case class TLARequiredAction(body: TLAExpression, vars: TLAExpression)
    extends TLAExpression

final case class TLAFairness(
    kind: TLAFairness.Kind,
    vars: TLAExpression,
    expression: TLAExpression,
) extends TLAExpression

object TLAFairness {
  sealed abstract class Kind
  case object StrongFairness extends Kind
  case object WeakFairness extends Kind
}

final case class TLAFunction(
    args: List[TLAQuantifierBound],
    body: TLAExpression,
) extends TLAExpression

final case class TLAFunctionCall(
    function: TLAExpression,
    params: List[TLAExpression],
) extends TLAExpression

final case class TLAFunctionSet(from: TLAExpression, to: TLAExpression)
    extends TLAExpression

final case class TLAFunctionSubstitution(
    source: TLAExpression,
    substitutions: List[TLAFunctionSubstitutionPair],
) extends TLAExpression

final case class TLAFunctionSubstitutionPair(
    anchor: TLAFunctionSubstitutionPairAnchor,
    keys: List[TLAFunctionSubstitutionKey],
    value: TLAExpression,
) extends TLANode {
  require(keys.nonEmpty)
}

final case class TLAFunctionSubstitutionKey(indices: List[TLAExpression])
    extends TLANode {
  require(indices.nonEmpty)
}

final case class TLAFunctionSubstitutionPairAnchor()
    extends TLANode
    with RefersTo.HasReferences {
  override def canonicalIdString: String = "@"
}

final case class TLAFunctionSubstitutionAt()
    extends TLAExpression
    with RefersTo[TLAFunctionSubstitutionPairAnchor]

trait TLAQuantified {
  def bounds: List[TLAQuantifierBound]
  def body: TLAExpression
}

final case class TLAQuantifiedExistential(
    bounds: List[TLAQuantifierBound],
    body: TLAExpression,
) extends TLAExpression
    with TLAQuantified

final case class TLAQuantifiedUniversal(
    bounds: List[TLAQuantifierBound],
    body: TLAExpression,
) extends TLAExpression
    with TLAQuantified

trait TLAUnquantified {
  def ids: List[TLADefiningIdentifier]
  def body: TLAExpression
}

final case class TLAExistential(
    ids: List[TLADefiningIdentifier],
    body: TLAExpression,
) extends TLAExpression
    with TLAUnquantified

final case class TLAUniversal(
    ids: List[TLADefiningIdentifier],
    body: TLAExpression,
) extends TLAExpression
    with TLAUnquantified

final case class TLASetConstructor(contents: List[TLAExpression])
    extends TLAExpression

final case class TLASetRefinement(
    binding: TLAQuantifierBound,
    when: TLAExpression,
) extends TLAExpression

final case class TLASetComprehension(
    body: TLAExpression,
    bounds: List[TLAQuantifierBound],
) extends TLAExpression

final case class TLATuple(elements: List[TLAExpression]) extends TLAExpression

final case class TLARecordConstructor(fields: List[TLARecordConstructorField])
    extends TLAExpression {
  require(fields.nonEmpty)
}

final case class TLARecordConstructorField(
    name: TLAIdentifier,
    value: TLAExpression,
) extends TLANode

final case class TLARecordSet(fields: List[TLARecordSetField])
    extends TLAExpression {
  require(fields.nonEmpty)
}

final case class TLARecordSetField(name: TLAIdentifier, set: TLAExpression)
    extends TLANode

final case class TLAChoose(
    ids: List[TLADefiningIdentifier],
    tpe: TLAChoose.Type,
    body: TLAExpression,
) extends TLAExpression {
  require(ids.nonEmpty, "TLA+ choose syntax must have at least one ID")
  tpe match {
    case TLAChoose.Id =>
      require(
        ids.size == 1,
        "the TLA+ CHOOSE syntax can have only one ID without tuple, eg << id1, id2 >>",
      )
    case TLAChoose.Tuple => // no other requirements here
  }
}

object TLAChoose {
  sealed abstract class Type
  case object Id extends Type
  case object Tuple extends Type
}

final case class TLAQuantifiedChoose(
    binding: TLAQuantifierBound,
    body: TLAExpression,
) extends TLAExpression

final case class TLALambda(
    idents: List[TLADefiningIdentifier],
    body: TLAExpression,
) extends TLAExpression
