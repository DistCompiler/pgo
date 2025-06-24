package pgo.parser

import pgo.model.Definition.{ScopeIdentifier, ScopeIdentifierName}
import pgo.model.mpcal.{MPCalCall, MPCalRefExpr}
import pgo.model.pcal.{PCalAssignmentLhsIdentifier, PCalCall, PCalMacroCall}
import pgo.model.{Definition, DefinitionComposite, DefinitionOne, Visitable}
import pgo.model.tla._

import scala.annotation.tailrec
import scala.collection.mutable
import pgo.util.TLC
import scala.util.Using
import pgo.model.PGoError
import pgo.model.SourceLocation.UnderlyingString
import scala.collection.View
import pgo.model.QualifiedDefinition
import pgo.util.Description.*

final case class TLAParserContext(
    minColumn: Int = -1,
    lateBindingStack: Int = 0,
    currentScope: Map[Definition.ScopeIdentifier, DefinitionOne] = Map.empty,
    recursiveOperators: Map[Definition.ScopeIdentifier, TLARecursive.Decl] =
      Map.empty,
    functionSubstitutionPairAnchor: Option[TLAFunctionSubstitutionPairAnchor] =
      None,
) {
  def withMinColumn(minColumn: Int): TLAParserContext =
    copy(minColumn = minColumn)

  def withDefinition(defn: Definition): TLAParserContext =
    defn match {
      case defn: TLAOperatorDefinition
          if currentScope
            .get(defn.identifier)
            .exists(_.isInstanceOf[TLARecursive.Decl]) =>
        val decl = currentScope(defn.identifier).asInstanceOf[TLARecursive.Decl]
        // this fixes one thing: the recursive directive now properly refers to the operator defn
        // the full-module parser should then go on to properly update any already-made references to the recursive decl
        decl.setRefersTo(defn)
        copy(currentScope = currentScope.updated(defn.identifier, defn))
      case defn: DefinitionOne =>
        copy(currentScope = currentScope.updated(defn.identifier, defn))
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
    TLAParserContext.findModule(id) match
      case None =>
        throw ModuleNotFoundError(id)
      case Some(module) => module

  def lookupModuleDefinitions(
      id: Definition.ScopeIdentifierName,
  ): View[DefinitionOne] =
    lookupModule(id).moduleDefinitions(captureLocal = false)

  def instantiateModule(
      id: Definition.ScopeIdentifierName,
  ): TLAParserContext = {
    currentScope.get(id) match {
      case Some(defn: TLAModule) => ???
      case _                     => ???
    }
  }

  def lookupDefinition(
      path: List[Definition.ScopeIdentifier],
  ): Option[DefinitionOne] =
    path match {
      case Nil      => None
      case List(id) => currentScope.get(id)
      case id :: tl =>
        currentScope.get(id) match
          case None => None
          case Some(QualifiedDefinition(_, defn, _)) =>
            @scala.annotation.tailrec
            def impl(
                path: List[Definition.ScopeIdentifier],
                defn: DefinitionOne,
            ): Option[DefinitionOne] =
              (path, defn) match
                case (id :: tl, QualifiedDefinition(prefix, defn, _))
                    if id == prefix =>
                  impl(tl, defn)
                case _ => None

            impl(tl, defn)
          case Some(defn) =>
            throw KindMismatchError(
              id.sourceLocation,
              d"qualified reference to non-qualified definition ${defn.canonicalIdString}",
            )

    }
  end lookupDefinition
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
          val underlying = UnderlyingString(contents, path.toString)
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

  def findModule(name: Definition.ScopeIdentifierName): Option[TLAModule] =
    lazy val theActualModuleOpt =
      val vs = visitSet.get()
      vs.get(name.name.id) match
        case Some(origRef) =>
          throw RecursiveModuleError(origRef, name)
        case None =>
          vs += name.name.id -> name
          try
            findModuleInZip(
              name,
              TLC.theTools,
              _ / "tla2sany" / "StandardModules",
            )
              .orElse(findModuleInZip(name, TLC.theStandardModules))
              .orElse(findModuleInZip(name, TLC.theCommunityModules))
          finally vs -= name.name.id

    val accessorFn = moduleCache.synchronized(
      moduleCache.getOrElseUpdate(name.name.id, () => theActualModuleOpt),
    )
    accessorFn()
  end findModule
end TLAParserContext
