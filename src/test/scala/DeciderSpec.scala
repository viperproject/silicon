import collection.mutable.Stack
import org.scalatest._
import scala.Some
import semper.silicon.decider.DefaultDecider
import semper.silicon.reporting.DefaultContext
import semper.silicon.reporting.DependencyNotFoundException
import semper.silicon.state.DefaultState
import semper.silicon.state.DirectFieldChunk
import semper.silicon.state.FieldChunkIdentifier
import semper.silicon.state.MapBackedStore
import semper.silicon.state.SetBackedHeap
import semper.silicon.state.terms.DefaultFractionalPermissions
import semper.silicon.state._
import semper.silicon.reporting.DefaultContext
import semper.silicon.state.terms._
import semper.silicon.reporting.Bookkeeper
import semper.silicon.Config
import semper.silicon.reporting.DependencyNotFoundException
import semper.silicon.decider.SMTLib2PreambleEmitter
import semper.silicon.interfaces.decider.Decider
import semper.silicon.state.terms._


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

  def emitSetPreamble(decider:Decider[P, ST, H, PC, S, C]) {
    val preambleFileEmitter = new SMTLib2PreambleEmitter(decider.prover.asInstanceOf[semper.silicon.decider.Z3ProverStdIO])
    decider.prover.declare(terms.SortDecl(sorts.Set(sorts.Ref)))
    decider.prover.logComment(s"/sets_declarations_dafny.smt2 [Set[Ref]]")
    preambleFileEmitter.emitSortParametricAssertions("/sets_declarations_dafny.smt2", sorts.Ref)
    decider.prover.logComment(s"/sets_axioms_dafny.smt2 [Set[Ref]]")
    preambleFileEmitter.emitSortParametricAssertions("/sets_axioms_dafny.smt2", sorts.Ref)
  }


  it should "say that we have enough permissions for exhaling 'acc(x.f,1)' in case h: x.f -> _ # 1" in {
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

  it should "say that we have not enough permissions to access x.f if we do not know that it is in a set" in {
    val decider = createDecider
    emitSetPreamble(decider)

    val x = decider.fresh(sorts.Ref)
    val S = decider.fresh(sorts.Set(sorts.Ref))

    val heap = new SetBackedHeap() + DirectConditionalChunk("f", null, SetIn(*(), S), FullPerm())

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

  it should "say that we have enough permissions for exhaling 'acc(x.f, 0.5) in case h: y.f -> _ # 0.5, z.f -> _ # 0.5. π: (x==y || x==z)" in {
    val decider = createDecider

    val x,y,z = decider.fresh(sorts.Ref)

    decider.assume(Or(Eq(x,y), Eq(x,z)))

    val heap = new SetBackedHeap() + DirectFieldChunk(y, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))) ) + DirectFieldChunk(z, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))) )

    assert(decider.hasEnoughPermissionsGlobally(heap, FieldChunkIdentifier(x, "f"), FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2)))) === true)

    val exhaleHeap = new SetBackedHeap() + DirectFieldChunk(z, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))))
  }

  it should "let us exhale 'acc(x.f, 0.5) in case h: y.f -> _ # 0.5, z.f -> _ # 0.5. π: (x==y || x==z)" in {
    val decider = createDecider

    val x,y,z = decider.fresh(sorts.Ref)

    decider.assume(Or(Eq(x,y), Eq(x,z)))

    val heap = new SetBackedHeap() + DirectFieldChunk(y, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))) ) + DirectFieldChunk(z, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))) )

    assert(decider.hasEnoughPermissionsGlobally(heap, FieldChunkIdentifier(x, "f"), FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2)))) === true)

    val exhaleHeap = new SetBackedHeap() + DirectFieldChunk(x, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))))

    val h = decider.exhalePermissions(heap, exhaleHeap)
    h match {
      case None => fail("exhale should not fail!")
      case Some(_) =>
    }
  }



  it should "let us exhale 'acc(x.f, 1) in case h: y.f -> _ # 0.5, z.f -> _ # 0.5. π: (x==y && x==z)" in {
    val decider = createDecider

    val x,y,z = decider.fresh(sorts.Ref)

    decider.assume(And(Eq(x,y), Eq(x,z)))

    val heap = new SetBackedHeap() + DirectFieldChunk(y, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))) ) + DirectFieldChunk(z, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))) )

    assert(decider.hasEnoughPermissionsGlobally(heap, FieldChunkIdentifier(x, "f"), FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2)))) === true)

    val exhaleHeap = new SetBackedHeap() + DirectFieldChunk(x, "f", null, FullPerm())

    val h = decider.exhalePermissions(heap, exhaleHeap)
    h match {
      case None => fail("exhale should not fail!")
      case Some(_) =>
    }
  }

  it should "let us exhale 'acc(x.f, 0.5) in case h: y.f -> _ # 0.5, z.f -> _ # 0.5. π: (x==y || x==z), but not let us exhale 'acc(z.f,0.5)' on the resulting heap" in {
    val decider = createDecider

    val x,y,z = decider.fresh(sorts.Ref)

    decider.assume(Or(Eq(x,y), Eq(x,z)))

    val heap = new SetBackedHeap() + DirectFieldChunk(y, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))) ) + DirectFieldChunk(z, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))) )

    assert(decider.hasEnoughPermissionsGlobally(heap, FieldChunkIdentifier(x, "f"), FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2)))) === true)

    val exhaleHeap = new SetBackedHeap() + DirectFieldChunk(x, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))))

    val h = decider.exhalePermissions(heap, exhaleHeap)
    h match {
      case None => fail("exhale should not fail!")
      case Some(exhaledHeap) => {

        val exhaleHeap2 = new SetBackedHeap() + DirectFieldChunk(z, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))))

        val h2 = decider.exhalePermissions(exhaledHeap, exhaleHeap2)
        h2 match {
          case None =>
          case Some(_) => fail("exhale should fail!")
        }
      }
    }
  }

    it should "let us exhale a single object from a set" in {
      val decider = createDecider
      emitSetPreamble(decider)

      val x = decider.fresh(sorts.Ref)
      val S = decider.fresh(sorts.Set(sorts.Ref))

      decider.assume(SetIn(x, S))

      val heap = new SetBackedHeap() + DirectConditionalChunk("f", null, SetIn(*(), S), FullPerm())

      // TODO
      // assert(decider.hasEnoughPermissionsGlobally(heap, FieldChunkIdentifier(x, "f"), FullPerm()) === true)

      val exhaleHeap = new SetBackedHeap() + DirectFieldChunk(x, "f", null, FullPerm())

      val h = decider.exhalePermissions(heap, exhaleHeap)
      h match {
        case None => fail("exhale should not fail!")
        case _ =>
      }
    }

  it should "not let us exhale a single object x when there is a set chunk S, but we do not have the info that x is in S" in {
    val decider = createDecider
    emitSetPreamble(decider)

    val x = decider.fresh(sorts.Ref)
    val S = decider.fresh(sorts.Set(sorts.Ref))

    val heap = new SetBackedHeap() + DirectConditionalChunk("f", null, SetIn(*(), S), FullPerm())

    // TODO
    // assert(decider.hasEnoughPermissionsGlobally(heap, FieldChunkIdentifier(x, "f"), FullPerm()) === true)

    val exhaleHeap = new SetBackedHeap() + DirectFieldChunk(x, "f", null, FullPerm())

    val h = decider.exhalePermissions(heap, exhaleHeap)
    h match {
      case None =>
      case _ => fail("exhale should fail!")
    }
  }

  it should "let us exhale a set from set chunks" in  {
    val decider = createDecider
    emitSetPreamble(decider)

    val S,T,U = decider.fresh(sorts.Set(sorts.Ref))

    decider.assume(SetSubset(U, SetIntersection(S, T)))

    val heap = new SetBackedHeap() + DirectConditionalChunk("f", null, SetIn(*(), S), FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2)))) + DirectConditionalChunk("f", null, SetIn(*(), T), FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))))

    // TODO
    // assert(decider.hasEnough...)

    val exhaleHeap = new SetBackedHeap() + DirectConditionalChunk("f", null, SetIn(*(), U), FullPerm())

    val h = decider.exhalePermissions(heap, exhaleHeap)
    h match {
      case None => fail("exhale should succeed!")
      case Some(exhaledHeap) =>  decider.exhalePermissions(exhaledHeap, exhaleHeap) match {
        case None =>
        case _ => fail("exhale should fail!")
      }
    }
  }

  it should "let us exhale a set from field chunks" in {
    val decider = createDecider
    emitSetPreamble(decider)

    val x,y = decider.fresh(sorts.Ref)
    val S = decider.fresh(sorts.Set(sorts.Ref))

    decider.assume(Eq(S, SetUnion(SingletonSet(x), SingletonSet(y))))

    val heap = new SetBackedHeap + DirectFieldChunk(x, "f", null, FullPerm()) + DirectFieldChunk(y, "f", null, FullPerm())


    val exhaleHeap = new SetBackedHeap() + DirectConditionalChunk("f", null, SetIn(*(), S), FullPerm())

    val h = decider.exhalePermissions(heap, exhaleHeap)
    h match {
      case None => fail("exhale should succeed!")
      case _ =>
    }
  }

  it should "not let us exhale a set from field chunks when there are not enough permissions" in {
    val decider = createDecider
    emitSetPreamble(decider)

    val x,y = decider.fresh(sorts.Ref)
    val S = decider.fresh(sorts.Set(sorts.Ref))

    decider.assume(Eq(S, SetUnion(SingletonSet(x), SingletonSet(y))))

    val heap = new SetBackedHeap + DirectFieldChunk(x, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2)))) + DirectFieldChunk(y, "f", null, FractionPerm(TermPerm(IntLiteral(1)),TermPerm(IntLiteral(2))))


    val exhaleHeap = new SetBackedHeap() + DirectConditionalChunk("f", null, SetIn(*(), S), FullPerm())

    val h = decider.exhalePermissions(heap, exhaleHeap)
    h match {
      case None =>
      case _ =>  fail("exhale should fail!")
    }
  }

  it should "not let us exhale two sets from a set chunk when we do not know that these sets are disjoint" in  {
    val decider = createDecider
    emitSetPreamble(decider)

    val S,T,U = decider.fresh(sorts.Set(sorts.Ref))

    decider.assume(SetSubset(T, S))
    decider.assume(SetSubset(U, S))

    val heap = new SetBackedHeap() + DirectConditionalChunk("f", null, SetIn(*(), S), FullPerm())

    // TODO
    // assert(decider.hasEnough...)

    val exhaleHeap = new SetBackedHeap() + DirectConditionalChunk("f", null, SetIn(*(), T), FullPerm())
    val exhaleHeap2 = new SetBackedHeap() + DirectConditionalChunk("f", null, SetIn(*(), U), FullPerm())


    val h = decider.exhalePermissions(heap, exhaleHeap)
    h match {
      case None => fail("exhale should succeed!")
      case Some(exhaledHeap) =>  decider.exhalePermissions(exhaledHeap, exhaleHeap2) match {
        case None =>
        case _ => fail("exhale should fail!")
      }
    }
  }

  it should "let us exhale two sets from a set chunk when we do know that these sets are disjoint" in  {
    val decider = createDecider
    emitSetPreamble(decider)

    val S,T,U = decider.fresh(sorts.Set(sorts.Ref))

    decider.assume(SetSubset(T, S))
    decider.assume(SetSubset(U, S))
    decider.assume(SetDisjoint(T,U))

    val heap = new SetBackedHeap() + DirectConditionalChunk("f", null, SetIn(*(), S), FullPerm())

    // TODO
    // assert(decider.hasEnough...)

    val exhaleHeap = new SetBackedHeap() + DirectConditionalChunk("f", null, SetIn(*(), T), FullPerm())
    val exhaleHeap2 = new SetBackedHeap() + DirectConditionalChunk("f", null, SetIn(*(), U), FullPerm())


    val h = decider.exhalePermissions(heap, exhaleHeap)
    h match {
      case None => fail("exhale should succeed!")
      case Some(exhaledHeap) =>  decider.exhalePermissions(exhaledHeap, exhaleHeap2) match {
        case None =>  fail("exhale should succeed!")
        case _ =>
      }
    }
  }

 }