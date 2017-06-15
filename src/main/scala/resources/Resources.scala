package viper.silicon.resources

/**
  * Created by Robin on 12.06.17.
  */
object Resources {

  val resourceDescriptions: Map[ResourceID, ResourceDescription] = Map(PredicateID() -> new PredicateDescription, FieldID() -> new FieldDescription)

}

sealed abstract class ResourceID

case class PredicateID() extends ResourceID
case class FieldID() extends ResourceID
