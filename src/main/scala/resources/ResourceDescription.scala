package viper.silicon.resources

/**
  * Created by Robin on 10.06.17.
  */
abstract class ResourceDescription {

  val instanceProperties: Seq[BooleanExpression]
  val staticProperties: Seq[BooleanExpression]
  val delayedProperties: Seq[BooleanExpression]
  val mergeRequirements: Seq[BooleanExpression]
  val subtractRequirements: Seq[BooleanExpression]

  // TODO: Other properties?
  // TODO: heap-add, heap-remove methods
}

class PredicateDescription extends ResourceDescription {

  override val instanceProperties = Seq(permAtLeastZero)
  override val staticProperties = Seq()
  override val delayedProperties = Seq(valNeqImpliesLocNeq)
  override val mergeRequirements = Seq(locSame)
  override val subtractRequirements = Seq(locSame)

  def locSame: BooleanExpression = Equals(LocationAccess(This()), LocationAccess(ChunkVariable("c")))

  def permAtLeastZero: BooleanExpression = GreaterThanEquals(PermissionAccess(This()), PermissionLiteral(0, 1))

  def valNeqImpliesLocNeq: BooleanExpression = {
    val c1 = ChunkVariable("c1")
    val c2 = ChunkVariable("c2")
    ForEach(Seq(c1, c2), Check(NotEquals(ValueAccess(c1), ValueAccess(c2)), NotEquals(LocationAccess(c1), LocationAccess(c2)), True()))
  }

}

class FieldDescription extends PredicateDescription {

  override val instanceProperties = Seq(permAtLeastZero, permAtMostOne, permImpliesNonNull)
  override val delayedProperties = Seq(valNeqImpliesLocNeq, permUpperBoundDiseq)

  def permAtMostOne: BooleanExpression = LessThanEquals(PermissionAccess(This()), PermissionLiteral(1, 1))

  def permImpliesNonNull: BooleanExpression = {
    Implies(GreaterThan(PermissionAccess(This()), PermissionLiteral(0, 1)), NotEquals(LocationAccess(This()), Null()))
  }

  def permUpperBoundDiseq: BooleanExpression = {
    val perm1 = PermissionAccess(ChunkVariable("c1"))
    val perm2 = PermissionAccess(ChunkVariable("c2"))
    val greaterThan = GreaterThan(Plus(perm1, perm2), PermissionLiteral(1, 1))
    val neq = NotEquals(LocationAccess(ChunkVariable("c1")), LocationAccess(ChunkVariable("c2")))
    ForEach(Seq(ChunkVariable("c1"), ChunkVariable("c2")), Check(greaterThan, neq, True()))
  }


}

