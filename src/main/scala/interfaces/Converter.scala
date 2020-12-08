import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.{Store, Heap, State}
import viper.silver.verifier.{Counterexample, Model, VerificationError, SingleEntry}
import viper.silicon.state.terms.Term


class Converter(model: Model, store: Store, heap: Heap, oldHeaps: State.OldHeaps){
    val extModel : ExtModel = ???}

/* basically I dont want to lose information since I may not process all
of their types, so this type should still be able to represent the previous
models but give some additional functionality
Should probably be implemented in silver as child class of current model entries */

sealed trait ExtModelEntry
case class LitIntEntry(value: Int) extends ExtModelEntry 
case class LitBoolEntry(value: Boolean) extends ExtModelEntry
case class RefEntry(fields: Map[String, ExtModelEntry])
case class ExtMapEntry(options: Map[String, ExtModelEntry])
case class Other(value: String)

class ExtModelVar(name: String, label: String)
class ExtModel(entries: Map[ExtModelVar, ExtModelEntry]){

}