package pgo.model.tla

sealed abstract class TLAModuleExtends extends TLADefinitionComposite {
  def identifier: TLAIdentifier
}

final case class TLAModuleExtendsBuiltin(module: TLABuiltinModules.TLABuiltinModule) extends TLAModuleExtends {
  override def identifier: TLAIdentifier = module.identifier

  override def members: List[TLADefinition] = module.members
}
final case class TLAModuleExtendsModule(module: TLAModule) extends TLAModuleExtends {
  override def identifier: TLAIdentifier = module.name

  override def members: List[TLADefinition] = module.definitions
}
