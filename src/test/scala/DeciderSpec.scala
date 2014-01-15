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

  def emitMultisetPreamble(decider:Decider[P, ST, H, PC, S, C]) {
    val preambleFileEmitter = new SMTLib2PreambleEmitter(decider.prover.asInstanceOf[semper.silicon.decider.Z3ProverStdIO])
    decider.prover.declare(terms.SortDecl(sorts.Multiset(sorts.Ref)))
    decider.prover.logComment(s"/multisets_declarations_dafny.smt2 [Multiset[Ref]]")
    preambleFileEmitter.emitSortParametricAssertions("/multisets_declarations_dafny.smt2", sorts.Ref)
    decider.prover.logComment(s"/multisets_axioms_dafny.smt2 [Multiset[Ref]]")
    preambleFileEmitter.emitSortParametricAssertions("/multisets_axioms_dafny.smt2", sorts.Ref)
  }

  def emitSequencePreamble(decider:Decider[P, ST, H, PC, S, C]) {
    val preambleFileEmitter = new SMTLib2PreambleEmitter(decider.prover.asInstanceOf[semper.silicon.decider.Z3ProverStdIO])
    decider.prover.declare(terms.SortDecl(sorts.Seq(sorts.Ref)))
    decider.prover.logComment(s"/sequences_declarations_dafny.smt2 [Seq[Ref]]")
    preambleFileEmitter.emitSortParametricAssertions("/sequences_declarations_dafny.smt2", sorts.Ref)
    decider.prover.logComment(s"/sequences_axioms_dafny.smt2 [Seq[Ref]]")
    preambleFileEmitter.emitSortParametricAssertions("/sequences_axioms_dafny.smt2", sorts.Ref)
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

  it should "let us do a basic exhale for Multisets!" in {
    val decider = createDecider
    emitSetPreamble(decider)
    emitMultisetPreamble(decider)

    val S,T = decider.fresh(sorts.Multiset(sorts.Ref))

    decider.assume(MultisetSubset(S,T))

    val heap = new SetBackedHeap() + DirectConditionalChunk("f", null /* we dont care about the value */, MultisetIn(*(), T), PermTimes(FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(8))), TermPerm(MultisetCount(*(), T))))

    val exhaleHeap = new SetBackedHeap() + DirectConditionalChunk("f", null, MultisetIn(*(), S), PermTimes(FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(8))), TermPerm(MultisetCount(*(), S))))

    val h = decider.exhalePermissions(heap, exhaleHeap)
    h match {
      case None => fail("exhale should succeed!")
      case Some(exhaledHeap) =>
    }
  }

  it should "let do us a complex exhale for Multisets!" in {
    val decider = createDecider
    emitSetPreamble(decider)
    emitMultisetPreamble(decider)

    val t = decider.fresh(sorts.Ref)
    val S,T = decider.fresh(sorts.Multiset(sorts.Ref))

    decider.assume(MultisetSubset(S,T))
    decider.assume(MultisetIn(t, T))
    decider.assume(Not(MultisetIn(t, S)))

    val heap = new SetBackedHeap() + DirectConditionalChunk("f", null /* we dont care about the value */, MultisetIn(*(), T), PermTimes(FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(16))), TermPerm(MultisetCount(*(), T))))

    val exhaleHeap1 = new SetBackedHeap() + DirectFieldChunk(t, "f", null, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(16))))
    val exhaleHeap2 = new SetBackedHeap() + DirectConditionalChunk("f", null, MultisetIn(*(), S), PermTimes(FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(16))), TermPerm(MultisetCount(*(), S))))

    decider.exhalePermissions(heap, exhaleHeap1) match {
      case None => fail("exhale should succeed!")
      case Some(exhaledHeap) => decider.exhalePermissions(exhaledHeap, exhaleHeap2) match {
        case None => fail("exhale should succeed!")
        case _ =>
      }
    }

  }

  it should "be possible to split a sequence in two parts" in {
    val decider = createDecider
    emitSetPreamble(decider)
    emitMultisetPreamble(decider)
    emitSequencePreamble(decider)

    val S = decider.fresh(sorts.Seq(sorts.Ref))
    val k = decider.fresh(sorts.Int)
    decider.assume(Less(k,SeqLength(S)))
    decider.assume(Not(Less(k, IntLiteral(0))))

    val heap = new SetBackedHeap() + DirectConditionalChunk("f", null, SeqIn(S, *()), PermTimes(FullPerm(), TermPerm(MultisetCount(*(), MultisetFromSeq(S)))) )

    val S1 = SeqTake(S, k)
    val S2 = SeqDrop(S, k)

    val exhaleHeap1 = new SetBackedHeap + DirectConditionalChunk("f", null, SeqIn(S1, *()), PermTimes(FullPerm(), TermPerm(MultisetCount(*(), MultisetFromSeq(S1)))))
    val exhaleHeap2 = new SetBackedHeap + DirectConditionalChunk("f", null, SeqIn(S2, *()), PermTimes(FullPerm(), TermPerm(MultisetCount(*(), MultisetFromSeq(S2)))))


    decider.exhalePermissions(heap, exhaleHeap1) match {
      case None => fail("exhale should succeed!")
      case Some(exhaledHeap) => decider.exhalePermissions(exhaledHeap, exhaleHeap2) match {
        case None => fail("exhale should succeed!")
        case Some(rest) =>
      }
    }

  }

  it should "be possible to exhale two elements with known indices from a sequence" in {
    val decider = createDecider
    emitSetPreamble(decider)
    emitMultisetPreamble(decider)
    emitSequencePreamble(decider)

    val S = decider.fresh(sorts.Seq(sorts.Ref))
    val k, l = decider.fresh(sorts.Int)
    decider.assume(Less(k,SeqLength(S)))
    decider.assume(Not(Less(k, IntLiteral(0))))
    decider.assume(Less(l,SeqLength(S)))
    decider.assume(Not(Less(l, IntLiteral(0))))
    decider.assume(Not(Eq(k,l)))

    val heap = new SetBackedHeap() + DirectConditionalChunk("f", null, SeqIn(S, *()), PermTimes(FullPerm(), TermPerm(MultisetCount(*(), MultisetFromSeq(S)))) )
    val exhaleHeap1 = new SetBackedHeap + DirectConditionalChunk("f", null, Eq(*(), SeqAt(S, k)), FullPerm())
    val exhaleHeap2 = new SetBackedHeap + DirectConditionalChunk("f", null, Eq(*(), SeqAt(S, l)), FullPerm())


    decider.exhalePermissions(heap, exhaleHeap1) match {
      case None => fail("exhale should succeed!")
      case Some(exhaledHeap) => println(exhaledHeap)
        decider.exhalePermissions(exhaledHeap, exhaleHeap2) match {
        case None => fail("exhale should succeed!")
        case Some(_) =>
      }
    }

  }

  it should "be possible to give permission to certain parts of the array, and then split it" in {
    val decider = createDecider
    emitSetPreamble(decider)
    emitMultisetPreamble(decider)
    emitSequencePreamble(decider)

    val S = decider.fresh(sorts.Seq(sorts.Ref))
    val start, end, k = decider.fresh(sorts.Int)

    decider.assume(AtLeast(IntLiteral(0), start))
    decider.assume(AtMost(start, end))
    decider.assume(Less(end, SeqLength(S)))
    // start <= k <= end
    decider.assume(AtLeast(k, start))
    decider.assume(AtMost(k, end))

    val heap = new SetBackedHeap() + DirectConditionalChunk("f", null, SeqIn(SeqDrop(SeqTake(S, end), start), *()), PermTimes(FullPerm(), TermPerm(MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(S, end), start))))))

    val S1 = SeqDrop(SeqTake(S, k), start)
    val S2 = SeqDrop(SeqTake(S, end), k)

    val exhaleHeap1 = new SetBackedHeap() + DirectConditionalChunk("f", null, SeqIn(S1, *()), PermTimes(FullPerm(), TermPerm(MultisetCount(*(), MultisetFromSeq(S1)))))
    val exhaleHeap2 = new SetBackedHeap() + DirectConditionalChunk("f", null, SeqIn(S2, *()), PermTimes(FullPerm(), TermPerm(MultisetCount(*(), MultisetFromSeq(S2)))))


    decider.exhalePermissions(heap, exhaleHeap2) match {
      case None =>fail("exhale should succeed!")
      case Some(exhaledHeap) => decider.exhalePermissions(exhaledHeap, exhaleHeap1) match {
        case None => fail("exhale should succeed")
        case Some(exhaledHeap2) =>
      }
    }
  }

  it should "be possible to write an index in an array" in {
    val decider = createDecider
    emitSetPreamble(decider)
    emitMultisetPreamble(decider)
    emitSequencePreamble(decider)

    val S= decider.fresh(sorts.Seq(sorts.Ref))
    val start, end, k = decider.fresh(sorts.Int)

    decider.assume(AtLeast(IntLiteral(0), start))
    decider.assume(AtMost(start, end))
    decider.assume(Less(end, SeqLength(S)))
    // start <= k <= end
    decider.assume(AtLeast(k, start))
    decider.assume(Less(k, end))

    val heap = new SetBackedHeap() + DirectConditionalChunk("f", null, SeqIn(SeqDrop(SeqTake(S, end), start), *()), PermTimes(FullPerm(), TermPerm(MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(S, end), start))))))

    val exhaleHeap1 = new SetBackedHeap + DirectConditionalChunk("f", null, Eq(*(), SeqAt(S, k)), FullPerm())

    decider.exhalePermissions(heap, exhaleHeap1) match {
      case None => fail("exhale should succeed!")
      case Some(exhaledHeap) => decider.exhalePermissions(exhaledHeap + DirectConditionalChunk("f", null, Eq(*(), SeqAt(S,k)), FullPerm()), heap) match {
        case None => fail("exhale should succeed!")
        case Some(done) => // yipyip
          //println(done)
      }
    }
  }

  /*it should "wildcards" in {
    val decider = createDecider
    emitSetPreamble(decider)
    emitMultisetPreamble(decider)
    emitSequencePreamble(decider)

    val a,b= decider.fresh(sorts.Ref)

    val ch1 = DirectFieldChunk(x, "f", null, WildcardPerm())
    val ch2 = DirectFieldChunk(y, "f", null, WildcardPerm())

  }*/

  it should "be possible to exhale elements with unknown indices"  in {

  }

  it should "be possible to split and do something extra for the element in the middle"  in {

  }

 }