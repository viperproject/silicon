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

  it should "say that we have  enough permissions for exhaling 'acc(x.f,1)' in case h: x.f -> _ # 1" in {
    val decider = createDecider

    // tr.f -> tv # al
    val x = decider.fresh(sorts.Ref)
    
    val heap = new SetBackedHeap() + DirectFieldChunk(x, "f", null, FullPerm())
    
    // h, id
    assert(decider.hasEnoughPermissionsGlobally(heap, FieldChunkIdentifier(x, "f"), FullPerm()) === true)
  }
  
  it should "say that we have not enough permissions for exhaling 'acc(x.f, 1) in case h: x.f -> _ # 0" in {
        val decider = createDecider

    val x = decider.fresh(sorts.Ref)
    // tr.f -> tv # al
    val heap = new SetBackedHeap() + DirectFieldChunk(x, "f", null, NoPerm())
    
    // h, id
    assert(decider.hasEnoughPermissionsGlobally(heap, FieldChunkIdentifier(x, "f"), FullPerm()) === false)
  }
  
     it should "say that we have enough permissions for exhaling 'acc(x.f, 0.5) in case h: y.f -> _ # 0.5, z.f -> _ # 0.5 π: {(x==y || x==z)}" in {
    val decider = createDecider

    val x,y,z = decider.fresh(sorts.Ref)
    
    // tr.f -> tv # al
    val heap = new SetBackedHeap() + DirectFieldChunk(y, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))) ) + DirectFieldChunk(z, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))) )
    decider.assume(Or(Eq(x,y), Eq(x,z)))

    
    // h, id
    assert(decider.hasEnoughPermissionsGlobally(heap, FieldChunkIdentifier(x, "f"), FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2)))) === true)
  }
  
   it should "say that we have not enough permissions for exhaling 'acc(x.f, 1) in case h: y.f -> _ # 0.5, z.f -> _ # 0.5 π: {}" in {
    val decider = createDecider

    val x,y,z = decider.fresh(sorts.Ref)
    
    // tr.f -> tv # al
    val heap = new SetBackedHeap() + DirectFieldChunk(y, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))) ) + DirectFieldChunk(z, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))) )
    
    // h, id
    assert(decider.hasEnoughPermissionsGlobally(heap, FieldChunkIdentifier(x, "f"), FullPerm()) === false)
  }
   
   it should "say that we have not enough permissions for exhaling 'acc(x.f, 1) in case h: y.f -> _ # 0.5, z.f -> _ # 0.5. π: (x==y || x==z) && y ≠ z" in {
    val decider = createDecider

    val x,y,z = decider.fresh(sorts.Ref)
    
    decider.assume(Or(Eq(x,y), Eq(x,z)))
    decider.assume(Not(Eq(y,z)))
    
    // tr.f -> tv # al
    val heap = new SetBackedHeap() + DirectFieldChunk(y, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))) ) + DirectFieldChunk(z, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))) )
    
    // h, id
    assert(decider.hasEnoughPermissionsGlobally(heap, FieldChunkIdentifier(x, "f"), FullPerm()) === false)
  }
}