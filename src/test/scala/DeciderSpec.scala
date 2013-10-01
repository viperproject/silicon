import collection.mutable.Stack
import org.scalatest._
import semper.silicon.decider.DefaultDecider
import semper.silicon.state.terms.DefaultFractionalPermissions
import semper.silicon.state.MapBackedStore
import semper.silicon.state.SetBackedHeap
import semper.silicon.state.MutableSetBackedPathConditions
import semper.silicon.state.DefaultState
import semper.silicon.reporting.DefaultContext
import semper.silicon.state.DirectFieldChunk
import semper.silicon.state.terms._
import semper.silicon.state.FieldChunkIdentifier
import semper.silicon.state.DefaultPathConditionsFactory
import semper.silicon.reporting.Bookkeeper
import semper.silicon.Config
import semper.silicon.reporting.DependencyNotFoundException
import semper.silicon.decider.SMTLib2PreambleEmitter
import semper.silicon.interfaces.decider.Decider


class DeciderSpec extends FlatSpec {

  behavior of "The decider"
  
  private type P = DefaultFractionalPermissions
  private type ST = MapBackedStore
  private type H = SetBackedHeap
  private type PC = MutableSetBackedPathConditions
  private type S = DefaultState[ST, H]
  private type C = DefaultContext[ST, H, S]

  // create objects needed by tests and return as a tuple
   def createDecider:Decider[P, ST, H, PC, S, C] = {
    val pathConditionsFactory = new DefaultPathConditionsFactory()
    val bookkeeper = new Bookkeeper()
    val config = new Config(Seq[String]())
    config initialize {case _ =>}
    
    val decider = new DefaultDecider[ST, H, PC, S, C]();
    decider.init(pathConditionsFactory, config, bookkeeper)
    decider.start().map(err => throw new DependencyNotFoundException(err)) 
    
    val preambleEmitter = new SMTLib2PreambleEmitter(decider.prover.asInstanceOf[semper.silicon.decider.Z3ProverStdIO])
    decider.prover.logComment("\n; /preamble.smt2")
    preambleEmitter.emitPreamble("/preamble.smt2")

    decider.pushScope()
    return decider
   } 

  it should "say that we have globally enough permission in case 1" in {
    val decider = createDecider

    // tr.f -> tv # al
    val heap = new SetBackedHeap() + DirectFieldChunk(Var("x", sorts.Ref), "f", Var("tx", sorts.Bool), FullPerm())
    
    // h, id
    assert(decider.hasEnoughPermissionsGlobally(heap, FieldChunkIdentifier(Var("x", sorts.Ref), "f"), FullPerm()) === true)
  }
  
  it should "say that we have not enough permissions in case 2" in {
        val decider = createDecider

    // tr.f -> tv # al
    val heap = new SetBackedHeap() + DirectFieldChunk(Var("x", sorts.Ref), "f", Var("tx", sorts.Bool), NoPerm())
    
    // h, id
    assert(decider.hasEnoughPermissionsGlobally(heap, FieldChunkIdentifier(Var("x", sorts.Ref), "f"), FullPerm()) === false)
  }
  
   it should "say that we have globally enough permission in case 3" in {
    val decider = createDecider

    // tr.f -> tv # al
    val heap = new SetBackedHeap() + DirectFieldChunk(Var("y", sorts.Ref), "f", Var("ty", sorts.Bool), FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))) ) + DirectFieldChunk(Var("z", sorts.Ref), "f", Var("tz", sorts.Bool), FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))) )
    
    // h, id
    assert(decider.hasEnoughPermissionsGlobally(heap, FieldChunkIdentifier(Var("x", sorts.Ref), "f"), FullPerm()) === true)
  }
}