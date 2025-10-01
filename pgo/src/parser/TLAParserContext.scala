package pgo.parser

import scala.collection.{View, mutable}
import scala.util.Using

import pgo.model.Definition.{ScopeIdentifier, ScopeIdentifierName}
import pgo.model.mpcal.MPCalRefExpr
import pgo.model.pcal.PCalAssignmentLhsIdentifier
import pgo.model.tla.*
import pgo.model.{
  Definition,
  DefinitionComposite,
  DefinitionOne,
  SourceLocation,
  Visitable,
}
import pgo.util.Description.*
import pgo.util.TLC

final case class TLAParserContext(
    underlyingText: SourceLocation.UnderlyingText,
    minColumn: Int = -1,
    lateBindingStack: Int = 0,
    currentScope: Map[String, DefinitionOne] = Map.empty,
    recursiveOperators: Map[String, TLARecursive.Decl] = Map.empty,
    functionSubstitutionPairAnchor: Option[TLAFunctionSubstitutionPairAnchor] =
      None,
) {
  def withMinColumn(minColumn: Int): TLAParserContext =
    copy(minColumn = minColumn)

  def withDefinition(defn: Definition): TLAParserContext =
    def safety(): Unit =
      val ddefn = defn.asInstanceOf[DefinitionOne]
      (ddefn.identifier.stringRepr, ddefn.canonicalIdString) match
        case ("-", "-_")              => // ok
        case (repr, id) if repr == id => // ok
        case (repr, id) =>
          throw AssertionError(s"internal error: binding $repr := $id")
    defn match {
      case defn: TLAOperatorDefinition
          if currentScope
            .get(defn.canonicalIdString)
            .exists(_.isInstanceOf[TLARecursive.Decl]) =>
        safety()
        val decl =
          currentScope(defn.canonicalIdString).asInstanceOf[TLARecursive.Decl]
        // this fixes one thing: the recursive directive now properly refers to the operator defn
        // the full-module parser should then go on to properly update any already-made references to the recursive decl
        decl.setRefersTo(defn)
        copy(currentScope = currentScope.updated(defn.canonicalIdString, defn))
      case defn: DefinitionOne =>
        safety()
        copy(currentScope = currentScope.updated(defn.canonicalIdString, defn))
      case defn: DefinitionComposite =>
        defn.singleDefinitions.foldLeft(this)(_.withDefinition(_))
    }

  def withFunctionSubstitutionPairAnchor(
      anchor: TLAFunctionSubstitutionPairAnchor,
  ): TLAParserContext =
    copy(functionSubstitutionPairAnchor = Some(anchor))

  def withLateBinding: TLAParserContext =
    copy(lateBindingStack = lateBindingStack + 1)

  /** match any "late bindings" (e.g bindings that are defined after use) up
    * with any unbound parts of the given AST node, or raise a binding error
    *
    * Note: this relies on know what things refer to other things, and should
    * hopefully work on PCal, MPCal, and TLA+, given references that work via
    * DefinitionOne
    *
    * @param visitable
    *   the AST node
    * @param defns
    *   the definitions to late-bind
    */
  def resolveLateBindings(
      visitable: Visitable,
      defns: IterableOnce[DefinitionOne],
  ): Unit = {
    val defnMap = defns.iterator.map(defn => defn.identifier -> defn).toMap

    // gather all nested unbound names
    // yes, this could end up being really slow, but last time I tried to be smart w/ mutable state or something,
    // a fuzz tester exposed a really weird bug
    val binders = mutable.ListBuffer[(ScopeIdentifier, DefinitionOne => Unit)]()
    visitable.visit(Visitable.TopDownFirstStrategy) {
      case ident @ TLAGeneralIdentifier(name, Nil) if !ident.hasRefersTo =>
        binders += ScopeIdentifierName(name) -> ident.setRefersTo
      case lhs @ PCalAssignmentLhsIdentifier(name) if !lhs.hasRefersTo =>
        binders += ScopeIdentifierName(name) -> lhs.setRefersTo
      case ref @ MPCalRefExpr(name, _) if !ref.hasRefersTo =>
        binders += ScopeIdentifierName(name) -> ref.setRefersTo
    }

    binders.foreach { case (ident, setRef) =>
      defnMap.get(ident) match {
        case Some(defn) => setRef(defn)
        case None       =>
          // if the late bindings count is 0 we should check that no idents remain unbound.
          // if so, raise the [AST traversal-wise, probably lexically] "earliest" one as an error.
          // otherwise, unbound idents may still be bound via currently unknown context, so don't do anything
          if (lateBindingStack == 0) {
            throw DefinitionLookupError(Nil, ident)
          }
      }
    }
  }

  def lookupModule(id: Definition.ScopeIdentifierName): TLAModule =
    val pwdOpt = underlyingText match
      case file: SourceLocation.UnderlyingFile =>
        Some(file.path / os.up)
      case _ => None
    TLAParserContext.findModule(id, pwdOpt) match
      case None =>
        throw ModuleNotFoundError(id)
      case Some(module) => module
  end lookupModule

  def lookupModuleDefinitions(
      id: Definition.ScopeIdentifierName,
  ): View[DefinitionOne] =
    lookupModule(id).moduleDefinitions(captureLocal = false)

  @scala.annotation.tailrec
  private def lookupDefinitionImpl(
      path: List[Definition.ScopeIdentifier],
      scope: Map[String, DefinitionOne],
  ): Option[DefinitionOne] =
    path match
      case Nil => None
      case List(id) =>
        scope.get(id.stringRepr) match
          case None =>
            None
          case Some(defn) =>
            if id.stringRepr != "-" && id.stringRepr != "self"
            then
              assert(
                id.stringRepr == defn.canonicalIdString,
                s"internal error: ${id.stringRepr} is bound to ${defn.canonicalIdString}",
              )
            Some(defn)
      case id :: tl =>
        scope.get(id.stringRepr) match
          case None =>
            None
          case Some(defn: TLAModuleDefinition) =>
            assert(
              id.stringRepr == defn.canonicalIdString,
              s"internal error: ${id.stringRepr} is bound to ${defn.canonicalIdString}",
            )
            lookupDefinitionImpl(tl, defn.localScope)
          case Some(defn) =>
            throw KindMismatchError(
              id.sourceLocation,
              d"qualified reference to non-qualified definition ${defn.canonicalIdString}",
            )
  end lookupDefinitionImpl

  def lookupDefinition(
      path: List[Definition.ScopeIdentifier],
  ): Option[DefinitionOne] =
    lookupDefinitionImpl(path, currentScope)
}

object TLAParserContext:
  private def findModuleInZip(
      name: Definition.ScopeIdentifierName,
      zipFile: os.Path,
      addPrefix: os.Path => os.Path = identity,
  ): Option[TLAModule] =
    val searchResult = Using.resource(os.zip.open(zipFile)): root =>
      val candidates = os.walk
        .stream(addPrefix(root))
        .filter(os.isFile)
        .filter(_.last.endsWith(".tla"))
        .filter(_.last == s"${name.name.id}.tla")
        .toList

      candidates match
        case List(path) =>
          val contents = os.read(path)
          val underlying =
            SourceLocation.UnderlyingString(contents, path.toString)
          Some((contents, underlying))
        case Nil => None
        case _ =>
          throw MultipleModuleDefinitionsError(name.sourceLocation, candidates)

    searchResult.map: (contents, underlying) =>
      TLAParser.readModule(underlying, contents)
  end findModuleInZip

  private val moduleCache = mutable.HashMap[String, () => Option[TLAModule]]()
  private val visitSet = ThreadLocal.withInitial(() =>
    mutable.HashMap[String, Definition.ScopeIdentifierName](),
  )

  private def findModuleInDir(
      dir: os.Path,
      name: Definition.ScopeIdentifierName,
  ): Option[TLAModule] =
    val path = dir / s"${name.name.id}.tla"
    if os.exists(path)
    then
      val contents = os.read(path)
      val underlying = SourceLocation.UnderlyingFile(path)
      Some(TLAParser.readModule(underlying, contents))
    else None
  end findModuleInDir

  def findModule(
      name: Definition.ScopeIdentifierName,
      pwdOpt: Option[os.Path] = None,
  ): Option[TLAModule] =
    lazy val theActualModuleOpt =
      val vs = visitSet.get()
      vs.get(name.name.id) match
        case Some(origRef) =>
          throw RecursiveModuleError(origRef, name)
        case None =>
          vs += name.name.id -> name
          try
            pwdOpt
              .flatMap(findModuleInDir(_, name))
              .orElse(findModuleInZip(name, TLC.theTLCModules))
              .orElse(findModuleInZip(name, TLC.theStandardModules))
              .orElse(findModuleInZip(name, TLC.theCommunityModules))
          finally vs -= name.name.id

    val accessorFn = moduleCache.synchronized(
      moduleCache.getOrElseUpdate(name.name.id, () => theActualModuleOpt),
    )
    accessorFn()
  end findModule
end TLAParserContext
