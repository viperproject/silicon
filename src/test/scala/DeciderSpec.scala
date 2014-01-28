import collection.mutable.Stack
import org.scalatest._
import scala.Some
import scala.Some
import scala.Some
import semper.silicon.decider.DefaultDecider
import semper.silicon.heap.{HeapManager, DefaultHeapManager}
import semper.silicon.interfaces.reporting.{TraceView, Context}
import semper.silicon.interfaces.state._
import semper.silicon.reporting._
import semper.silicon.reporting.DefaultContext
import semper.silicon.reporting.DependencyNotFoundException
import semper.silicon.state.DefaultState
import semper.silicon.state.DefaultState
import semper.silicon.state.DefaultState
import semper.silicon.state.DirectFieldChunk
import semper.silicon.state.DirectFieldChunk
import semper.silicon.state.DirectFieldChunk
import semper.silicon.state.QuantifiedChunk
import semper.silicon.state.QuantifiedChunk
import semper.silicon.state.FieldChunkIdentifier
import semper.silicon.state.FieldChunkIdentifier
import semper.silicon.state.FieldChunkIdentifier
import semper.silicon.state.MapBackedStore
import semper.silicon.state.MapBackedStore
import semper.silicon.state.MapBackedStore
import semper.silicon.state.SetBackedHeap
import semper.silicon.state.SetBackedHeap
import semper.silicon.state.SetBackedHeap
import semper.silicon.state.terms.*
import semper.silicon.state.terms.*
import semper.silicon.state.terms.DefaultFractionalPermissions
import semper.silicon.state._
import semper.silicon.state.terms._
import semper.silicon.Config
import semper.silicon.decider.SMTLib2PreambleEmitter
import semper.silicon.interfaces.decider.Decider
import semper.silicon.state.terms._
import semper.silicon.state.terms.DomainFApp
import semper.silicon.state.terms.DomainFApp
import semper.silicon.state.terms.FractionPerm
import semper.silicon.state.terms.FractionPerm
import semper.silicon.state.terms.FullPerm
import semper.silicon.state.terms.FullPerm
import semper.silicon.state.terms.IntLiteral
import semper.silicon.state.terms.IntLiteral
import semper.silicon.state.terms.NoPerm
import semper.silicon.state.terms.NoPerm
import semper.silicon.state.terms.Quantification
import semper.silicon.state.terms.Quantification
import semper.silicon.state.terms.SingletonSet
import semper.silicon.state.terms.SingletonSet
import semper.silicon.state.terms.TermPerm
import semper.silicon.state.terms.TermPerm
import semper.silicon.state.terms.Var
import semper.silicon.state.terms.Var


class DeciderSpec extends FlatSpec {

  behavior of "The decider"

  private type P = DefaultFractionalPermissions
  private type ST = MapBackedStore
  private type H = SetBackedHeap
  private type PC = MutableSetBackedPathConditions
  private type S = DefaultState[ST, H]
  private type C = DefaultContext[ST, H, S]
  private type TV = BranchingOnlyTraceView[ST, H, S]

  // create objects needed by tests and return as a tuple
  def createDecider: Decider[P, ST, H, PC, S, C] = {
    val pathConditionsFactory = new DefaultPathConditionsFactory()
    val bookkeeper = new Bookkeeper()
    val config = new Config(Seq[String]())
    config initialize {
      case _ =>
    }

    val decider = new DefaultDecider[ST, H, PC, S, C]();
    decider.init(pathConditionsFactory, config, bookkeeper)
    decider.start().map(err => throw new DependencyNotFoundException(err))

    val preambleEmitter = new SMTLib2PreambleEmitter(decider.prover.asInstanceOf[semper.silicon.decider.Z3ProverStdIO])
    decider.prover.logComment("\n; /preamble.smt2")
    preambleEmitter.emitPreamble("/preamble.smt2")

    decider.pushScope()
    return decider
  }

  def createHeapManager = {
    val decider = createDecider
    (new DefaultHeapManager[ST, H, PC, S, C, TV](decider, new DefaultSymbolConvert(), new DefaultStateFactory(decider.π _)), decider)
  }

  def emitSetPreamble(decider: Decider[P, ST, H, PC, S, C]) {
    val preambleFileEmitter = new SMTLib2PreambleEmitter(decider.prover.asInstanceOf[semper.silicon.decider.Z3ProverStdIO])
    decider.prover.declare(terms.SortDecl(sorts.Set(sorts.Ref)))
    decider.prover.logComment(s"/sets_declarations_dafny.smt2 [Set[Ref]]")
    preambleFileEmitter.emitSortParametricAssertions("/sets_declarations_dafny.smt2", sorts.Ref)
    decider.prover.logComment(s"/sets_axioms_dafny.smt2 [Set[Ref]]")
    preambleFileEmitter.emitSortParametricAssertions("/sets_axioms_dafny.smt2", sorts.Ref)
  }

  def emitMultisetPreamble(decider: Decider[P, ST, H, PC, S, C]) {
    val preambleFileEmitter = new SMTLib2PreambleEmitter(decider.prover.asInstanceOf[semper.silicon.decider.Z3ProverStdIO])
    decider.prover.declare(terms.SortDecl(sorts.Multiset(sorts.Ref)))
    decider.prover.logComment(s"/multisets_declarations_dafny.smt2 [Multiset[Ref]]")
    preambleFileEmitter.emitSortParametricAssertions("/multisets_declarations_dafny.smt2", sorts.Ref)
    decider.prover.logComment(s"/multisets_axioms_dafny.smt2 [Multiset[Ref]]")
    preambleFileEmitter.emitSortParametricAssertions("/multisets_axioms_dafny.smt2", sorts.Ref)
  }

  def emitSequencePreamble(decider: Decider[P, ST, H, PC, S, C]) {
    val preambleFileEmitter = new SMTLib2PreambleEmitter(decider.prover.asInstanceOf[semper.silicon.decider.Z3ProverStdIO])
    decider.prover.declare(terms.SortDecl(sorts.Seq(sorts.Ref)))
    decider.prover.logComment(s"/sequences_declarations_dafny.smt2 [Seq[Ref]]")
    preambleFileEmitter.emitSortParametricAssertions("/sequences_declarations_dafny.smt2", sorts.Ref)
    decider.prover.logComment(s"/sequences_axioms_dafny.smt2 [Seq[Ref]]")
    preambleFileEmitter.emitSortParametricAssertions("/sequences_axioms_dafny.smt2", sorts.Ref)
  }


  it should "say that we have enough permissions for exhaling 'acc(x.f,1)' in case h: x.f -> _ # 1" in {
    val (heapManager, decider) = createHeapManager

    // tr.f -> tv # al
    val x = decider.fresh(sorts.Ref)

    val heap = new SetBackedHeap() + DirectFieldChunk(x, "f", null, FullPerm())

    // h, id
    assert(decider.assert(heapManager.permission(heap, FieldChunkIdentifier(x, "f")) === FullPerm()))
  }

  it should "say that we have not enough permissions for exhaling 'acc(x.f, 1) in case h: x.f -> _ # 0" in {
    val (heapManager, decider) = createHeapManager


    val x = decider.fresh(sorts.Ref)
    // tr.f -> tv # al
    val heap = new SetBackedHeap() + DirectFieldChunk(x, "f", null, NoPerm())

    // h, id
    assert(!decider.assert(heapManager.permission(heap, FieldChunkIdentifier(x, "f")) === FullPerm()))
  }


  it should "say that we have enough permissions for exhaling 'acc(x.f, 0.5) in case h: y.f -> _ # 0.5, z.f -> _ # 0.5 π: {(x==y || x==z)}" in {
    val (heapManager, decider) = createHeapManager

    val x, y, z = decider.fresh(sorts.Ref)

    // tr.f -> tv # al
    val heap = new SetBackedHeap() + DirectFieldChunk(y, "f", null, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2)))) + DirectFieldChunk(z, "f", null, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))))
    decider.assume(Or(Eq(x, y), Eq(x, z)))


    // h, id
    assert(decider.assert(AtMost(FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))), heapManager.permission(heap, FieldChunkIdentifier(x, "f")))))
  }

  it should "say that we have not enough permissions for exhaling 'acc(x.f, 1) in case h: y.f -> _ # 0.5, z.f -> _ # 0.5 π: {}" in {
    val (heapManager, decider) = createHeapManager

    val x, y, z = decider.fresh(sorts.Ref)

    // tr.f -> tv # al
    val heap = new SetBackedHeap() + DirectFieldChunk(y, "f", null, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2)))) + DirectFieldChunk(z, "f", null, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))))

    // h, id
    assert(!decider.assert(AtMost(FullPerm(), heapManager.permission(heap, FieldChunkIdentifier(x, "f")))))
  }

  it should "say that we have not enough permissions for exhaling 'acc(x.f, 1) in case h: y.f -> _ # 0.5, z.f -> _ # 0.5. π: (x==y || x==z) && y ≠ z" in {
    val (heapManager, decider) = createHeapManager

    val x, y, z = decider.fresh(sorts.Ref)

    decider.assume(Or(Eq(x, y), Eq(x, z)))
    decider.assume(Not(Eq(y, z)))

    // tr.f -> tv # al
    val heap = new SetBackedHeap() + DirectFieldChunk(y, "f", null, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2)))) + DirectFieldChunk(z, "f", null, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))))

    // h, id
    assert(!decider.assert(AtMost(FullPerm(), heapManager.permission(heap, FieldChunkIdentifier(x, "f")))))
  }

  it should "say that we have enough permissions for exhaling 'acc(x.f, 0.5) in case h: y.f -> _ # 0.5, z.f -> _ # 0.5. π: (x==y || x==z)" in {
    val (heapManager, decider) = createHeapManager

    val x, y, z = decider.fresh(sorts.Ref)

    decider.assume(Or(Eq(x, y), Eq(x, z)))

    val heap = new SetBackedHeap() + DirectFieldChunk(y, "f", null, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2)))) + DirectFieldChunk(z, "f", null, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))))

    assert(decider.assert(AtMost(FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))), heapManager.permission(heap, FieldChunkIdentifier(x, "f")))))
  }

  it should "let us exhale 'acc(x.f, 0.5) in case h: y.f -> _ # 0.5, z.f -> _ # 0.5. π: (x==y || x==z)" in {
    val (heapManager, decider) = createHeapManager

    val x, y, z = decider.fresh(sorts.Ref)

    decider.assume(Or(Eq(x, y), Eq(x, z)))

    val heap = new SetBackedHeap() + DirectFieldChunk(y, "f", null, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2)))) + DirectFieldChunk(z, "f", null, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))))

    assert(decider.assert(AtMost(FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))), heapManager.permission(heap, FieldChunkIdentifier(x, "f")))))

    val exhale = QuantifiedChunk("f", null, TermPerm(Ite(*() === x, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))), NoPerm())))

    val h = heapManager.exhaleTest(heap, exhale) match {
      case None => fail("exhale should not fail!")
      case Some(_) =>
    }
  }



  it should "let us exhale 'acc(x.f, 1) in case h: y.f -> _ # 0.5, z.f -> _ # 0.5. π: (x==y && x==z)" in {
    val (heapManager, decider) = createHeapManager

    val x, y, z = decider.fresh(sorts.Ref)

    decider.assume(And(Eq(x, y), Eq(x, z)))

    val heap = new SetBackedHeap() + DirectFieldChunk(y, "f", null, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2)))) + DirectFieldChunk(z, "f", null, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))))

    assert(decider.assert(AtMost(FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))), heapManager.permission(heap, FieldChunkIdentifier(x, "f")))))

    val exhaleHeap = QuantifiedChunk("f", null, TermPerm(Ite(*() === x, FullPerm(), NoPerm())))

    val h = heapManager.exhaleTest(heap, exhaleHeap)
    h match {
      case None => fail("exhale should not fail!")
      case Some(_) =>
    }
  }

  it should "let us exhale 'acc(x.f, 0.5) in case h: y.f -> _ # 0.5, z.f -> _ # 0.5. π: (x==y || x==z), but not let us exhale 'acc(z.f,0.5)' on the resulting heap" in {
    val (heapManager, decider) = createHeapManager

    val x, y, z = decider.fresh(sorts.Ref)

    decider.assume(Or(Eq(x, y), Eq(x, z)))

    val heap = new SetBackedHeap() + DirectFieldChunk(y, "f", null, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2)))) + DirectFieldChunk(z, "f", null, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))))

    assert(decider.assert(AtMost(FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))), heapManager.permission(heap, FieldChunkIdentifier(x, "f")))))

    val exhaleHeap = QuantifiedChunk("f", null, TermPerm(Ite(*() === x, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))), NoPerm())))

    val h = heapManager.exhaleTest(heap, exhaleHeap)
    h match {
      case None => fail("exhale should not fail!")
      case Some(exhaledHeap) => {

        val exhaleHeap2 = QuantifiedChunk("f", null, TermPerm(Ite(z === *(), FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))), NoPerm())))

        val h2 = heapManager.exhaleTest(exhaledHeap, exhaleHeap2)
        h2 match {
          case None =>
          case Some(_) => fail("exhale should fail!")
        }
      }
    }
  }

  it should "let us exhale a single object from a set" in {
    val (heapManager, decider) = createHeapManager
    emitSetPreamble(decider)

    val x = decider.fresh(sorts.Ref)
    val S = decider.fresh(sorts.Set(sorts.Ref))

    decider.assume(SetIn(x, S))

    val heap = new SetBackedHeap() + QuantifiedChunk("f", null, TermPerm(Ite(SetIn(*(), S), FullPerm(), NoPerm())))

    val exhaleHeap = QuantifiedChunk("f", null, TermPerm(Ite(*() === x, FullPerm(), NoPerm())))

    val h = heapManager.exhaleTest(heap, exhaleHeap)
    h match {
      case None => fail("exhale should not fail!")
      case _ =>
    }
  }

  it should "not let us exhale a single object x when there is a set chunk S, but we do not have the info that x is in S" in {
    val (heapManager, decider) = createHeapManager
    emitSetPreamble(decider)

    val x = decider.fresh(sorts.Ref)
    val S = decider.fresh(sorts.Set(sorts.Ref))

    val heap = new SetBackedHeap() + QuantifiedChunk("f", null, TermPerm(Ite(SetIn(*(), S), FullPerm(), NoPerm())))

    // TODO
    // assert(decider.hasEnoughPermissionsGlobally(heap, FieldChunkIdentifier(x, "f"), FullPerm()) === true)

    val exhaleHeap = QuantifiedChunk("f", null, TermPerm(Ite(*() === x, FullPerm(), NoPerm())))

    val h = heapManager.exhaleTest(heap, exhaleHeap)
    h match {
      case None =>
      case _ => fail("exhale should fail!")
    }
  }

  it should "let us exhale a set from set chunks" in {
    val (heapManager, decider) = createHeapManager
    emitSetPreamble(decider)

    val S, T, U = decider.fresh(sorts.Set(sorts.Ref))

    decider.assume(SetSubset(U, SetIntersection(S, T)))

    val heap = new SetBackedHeap() + QuantifiedChunk("f", null, TermPerm(Ite(SetIn(*(), S), FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))), NoPerm()))) + QuantifiedChunk("f", null, TermPerm(Ite(SetIn(*(), T), FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))), NoPerm())))

    // TODO
    // assert(decider.hasEnough...)

    val exhaleHeap = QuantifiedChunk("f", null, (TermPerm(Ite(SetIn(*(), U), FullPerm(), NoPerm()))))

    val h = heapManager.exhaleTest(heap, exhaleHeap)
    h match {
      case None => fail("exhale should succeed!")
      case Some(exhaledHeap) => heapManager.exhaleTest(exhaledHeap, exhaleHeap) match {
        case None =>
        case _ => fail("exhale should fail!")
      }
    }
  }

  it should "let us exhale a set from field chunks" in {
    val (heapManager, decider) = createHeapManager
    emitSetPreamble(decider)

    val x, y = decider.fresh(sorts.Ref)
    val S = decider.fresh(sorts.Set(sorts.Ref))

    decider.assume(Eq(S, SetUnion(SingletonSet(x), SingletonSet(y))))

    val heap = new SetBackedHeap + DirectFieldChunk(x, "f", null, FullPerm()) + DirectFieldChunk(y, "f", null, FullPerm())


    val exhaleHeap = QuantifiedChunk("f", null, TermPerm(Ite(SetIn(*(), S), FullPerm(), NoPerm())))

    val h = heapManager.exhaleTest(heap, exhaleHeap)
    h match {
      case None => fail("exhale should succeed!")
      case _ =>
    }
  }

  it should "not let us exhale a set from field chunks when there are not enough permissions" in {
    val (heapManager, decider) = createHeapManager
    emitSetPreamble(decider)

    val x, y = decider.fresh(sorts.Ref)
    val S = decider.fresh(sorts.Set(sorts.Ref))

    decider.assume(Eq(S, SetUnion(SingletonSet(x), SingletonSet(y))))

    val heap = new SetBackedHeap + DirectFieldChunk(x, "f", null, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2)))) + DirectFieldChunk(y, "f", null, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))))


    val exhaleHeap = QuantifiedChunk("f", null, TermPerm(Ite(SetIn(*(), S), FullPerm(), NoPerm())))

    val h = heapManager.exhaleTest(heap, exhaleHeap)
    h match {
      case None =>
      case _ => fail("exhale should fail!")
    }
  }

  it should "not let us exhale two sets from a set chunk when we do not know that these sets are disjoint" in {
    val (heapManager, decider) = createHeapManager
    emitSetPreamble(decider)

    val S, T, U = decider.fresh(sorts.Set(sorts.Ref))

    decider.assume(SetSubset(T, S))
    decider.assume(SetSubset(U, S))

    val heap = new SetBackedHeap() + QuantifiedChunk("f", null, TermPerm(Ite(SetIn(*(), S), FullPerm(), NoPerm())))

    // TODO
    // assert(decider.hasEnough...)

    val exhaleHeap = QuantifiedChunk("f", null, TermPerm(Ite(SetIn(*(), T), FullPerm(), NoPerm())))
    val exhaleHeap2 = QuantifiedChunk("f", null, TermPerm(Ite(SetIn(*(), U), FullPerm(), NoPerm())))


    val h = heapManager.exhaleTest(heap, exhaleHeap)
    h match {
      case None => fail("exhale should succeed!")
      case Some(exhaledHeap) => heapManager.exhaleTest(exhaledHeap, exhaleHeap2) match {
        case None =>
        case _ => fail("exhale should fail!")
      }
    }
  }

  it should "let us exhale two sets from a set chunk when we do know that these sets are disjoint" in {
    val (heapManager, decider) = createHeapManager
    emitSetPreamble(decider)

    val S, T, U = decider.fresh(sorts.Set(sorts.Ref))

    decider.assume(SetSubset(T, S))
    decider.assume(SetSubset(U, S))
    decider.assume(SetDisjoint(T, U))

    val heap = new SetBackedHeap() + QuantifiedChunk("f", null, (TermPerm(Ite(SetIn(*(), S), FullPerm(), NoPerm()))))

    // TODO
    // assert(decider.hasEnough...)

    val exhaleHeap = QuantifiedChunk("f", null, (TermPerm(Ite(SetIn(*(), T), FullPerm(), NoPerm()))))
    val exhaleHeap2 = QuantifiedChunk("f", null, (TermPerm(Ite(SetIn(*(), U), FullPerm(), NoPerm()))))


    val h = heapManager.exhaleTest(heap, exhaleHeap)
    h match {
      case None => fail("exhale should succeed!")
      case Some(exhaledHeap) => heapManager.exhaleTest(exhaledHeap, exhaleHeap2) match {
        case None => fail("exhale should succeed!")
        case _ =>
      }
    }
  }

  it should "let us do a basic exhale for Multisets!" in {
    val (heapManager, decider) = createHeapManager
    emitSetPreamble(decider)
    emitMultisetPreamble(decider)

    val S, T = decider.fresh(sorts.Multiset(sorts.Ref))

    decider.assume(MultisetSubset(S, T))

    val heap = new SetBackedHeap() + QuantifiedChunk("f", null /* we dont care about the value */ , PermTimes(FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(8))), TermPerm(MultisetCount(*(), T))))

    val exhaleHeap = QuantifiedChunk("f", null, PermTimes(FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(8))), TermPerm(MultisetCount(*(), S))))

    val h = heapManager.exhaleTest(heap, exhaleHeap)
    h match {
      case None => fail("exhale should succeed!")
      case Some(exhaledHeap) =>
    }
  }



  it should "be possible to write an index in an array" in {
    val (heapManager, decider) = createHeapManager
    emitSetPreamble(decider)
    emitMultisetPreamble(decider)
    emitSequencePreamble(decider)

    val S = decider.fresh(sorts.Seq(sorts.Ref))
    val start, end, k = decider.fresh(sorts.Int)

    decider.assume(AtLeast(start, IntLiteral(0)))
    decider.assume(AtMost(start, end))
    decider.assume(Less(end, SeqLength(S)))
    // start <= k <= end
    decider.assume(AtLeast(k, start))
    decider.assume(Less(k, end))

    val ch = QuantifiedChunk("f", null, PermTimes(FullPerm(), TermPerm(MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(S, end), start))))))
    val heap = new SetBackedHeap() + ch

    val exhaleHeap1 = QuantifiedChunk("f", null, TermPerm(Ite(Eq(*(), SeqAt(S, k)), FullPerm(), NoPerm())))

    heapManager.exhaleTest(heap, exhaleHeap1) match {
      case None => fail("exhale should succeed!")
      case Some(exhaledHeap) => heapManager.exhaleTest(exhaledHeap + QuantifiedChunk("f", null, (TermPerm(Ite(Eq(*(), SeqAt(S, k)), FullPerm(), NoPerm())))), ch) match {
        case None => fail("exhale should succeed!")
        case Some(done) => // yipyip
        //println(done)
      }
    }
  }

  /*it should "wildcards" in {
    val (heapManager, decider) = createHeapManager
    emitSetPreamble(decider)
    emitMultisetPreamble(decider)
    emitSequencePreamble(decider)

    val a,b= decider.fresh(sorts.Ref)

    val ch1 = DirectFieldChunk(x, "f", null, WildcardPerm())
    val ch2 = DirectFieldChunk(y, "f", null, WildcardPerm())

  }*/

  it should "be possible to exhale elements with unknown indices" in {

  }

  it should "be possible to split and do something extra for the element in the middle" in {

  }

  it should "say that we have not enough permissions to access x.f if we do not know that it is in a set" in {
    val (heapManager, decider) = createHeapManager
    emitSetPreamble(decider)

    val x = decider.fresh(sorts.Ref)
    val S = decider.fresh(sorts.Set(sorts.Ref))

    val heap = new SetBackedHeap() + QuantifiedChunk("f", null, TermPerm(Ite(SetIn(*(), S), FullPerm(), NoPerm())))

    assert(!decider.assert(AtMost(FullPerm(), heapManager.permission(heap, FieldChunkIdentifier(x, "f")))))
  }

  it should "let do us a complex exhale for Multisets!" in {
    val (heapManager, decider) = createHeapManager
    emitSetPreamble(decider)
    emitMultisetPreamble(decider)

    val t = decider.fresh(sorts.Ref)
    val S, T = decider.fresh(sorts.Multiset(sorts.Ref))

    decider.assume(MultisetSubset(S, T))
    decider.assume(MultisetIn(t, T))
    decider.assume(Not(MultisetIn(t, S)))

    val heap = new SetBackedHeap() + QuantifiedChunk("f", null /* we dont care about the value */ , PermTimes(FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(16))), TermPerm(MultisetCount(*(), T))))

    val exhaleHeap1 = QuantifiedChunk("f", null, TermPerm(Ite(*() === t, FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(16))), NoPerm())))
    val exhaleHeap2 = QuantifiedChunk("f", null, PermTimes(FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(16))), TermPerm(MultisetCount(*(), S))))

    heapManager.exhaleTest(heap, exhaleHeap1) match {
      case None => fail("exhale should succeed!")
      case Some(exhaledHeap) => heapManager.exhaleTest(exhaledHeap, exhaleHeap2) match {
        case None => fail("exhale should succeed!")
        case _ =>
      }
    }

  }



  it should "indirection" in {
    val (heapManager, decider) = createHeapManager
    emitSetPreamble(decider)

    val S = decider.fresh("S", sorts.Set(sorts.Ref))
    val Svalue = decider.fresh("t", sorts.Arrow(sorts.Ref, sorts.Ref))

    val idx = Var("idx", sorts.Ref)
    val indirectionChunk = QuantifiedChunk("f", null, TermPerm(Ite(Quantification(Exists, List(idx), Eq(DomainFApp(Function(Svalue.id, sorts.Arrow(sorts.Ref, sorts.Ref)), List(idx)), *())), FullPerm(), NoPerm())))


    val heap = new SetBackedHeap() + QuantifiedChunk("a", Svalue, TermPerm(Ite(SetIn(*(), S), FullPerm(), NoPerm()))) + indirectionChunk

    heapManager.exhaleTest(heap, indirectionChunk) match {
      case None => fail("exhale should succeed!")
      case Some(exhaledHeap) =>
    }


  }

  it should "be possible to give permission to certain parts of the array, and then split it" in {
    val (heapManager, decider) = createHeapManager
    emitSetPreamble(decider)
    emitMultisetPreamble(decider)
    emitSequencePreamble(decider)

    val S = decider.fresh("S", sorts.Seq(sorts.Ref))
    val start, end, k = decider.fresh(sorts.Int)

    decider.assume(AtLeast(IntLiteral(0), start))
    decider.assume(AtMost(start, end))
    decider.assume(AtMost(end, SeqLength(S)))
    // start <= k <= end
    decider.assume(AtLeast(k, start))
    decider.assume(AtMost(k, end))

    //decider.assume(SeqBounds(S, start,k) === True())

    val heap = new SetBackedHeap() + QuantifiedChunk("f", null, PermTimes(FullPerm(), TermPerm(MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(S, end), start))))))

    val S1 = SeqDrop(SeqTake(S, k), start)
    val S2 = SeqDrop(SeqTake(S, end), k)

    val exhaleHeap1 = QuantifiedChunk("f", null, PermTimes(FullPerm(), TermPerm(MultisetCount(*(), MultisetFromSeq(S1)))))
    val exhaleHeap2 = QuantifiedChunk("f", null, PermTimes(FullPerm(), TermPerm(MultisetCount(*(), MultisetFromSeq(S2)))))


    heapManager.exhaleTest(heap, exhaleHeap2) match {
      case None => fail("exhale 1 should succeed!")
      case Some(exhaledHeap) => heapManager.exhaleTest(exhaledHeap, exhaleHeap1) match {
        case None => fail("exhale 2 should succeed")
        case Some(exhaledHeap2) =>
      }
    }
  }

  it should "be possible to exhale two elements with known indices from a sequence" in {
    val (heapManager, decider) = createHeapManager
    emitSetPreamble(decider)
    emitMultisetPreamble(decider)
    emitSequencePreamble(decider)

    val S = decider.fresh(sorts.Seq(sorts.Ref))
    val k, l = decider.fresh(sorts.Int)
    decider.assume(Less(k, SeqLength(S)))
    decider.assume(Not(Less(k, IntLiteral(0))))
    decider.assume(Less(l, SeqLength(S)))
    decider.assume(Not(Less(l, IntLiteral(0))))
    decider.assume(k !== l)

    val heap = new SetBackedHeap() + QuantifiedChunk("f", null, PermTimes(FullPerm(), TermPerm(MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(S, SeqLength(S)), IntLiteral(0)))))))
    //val exhaleHeap1 = new SetBackedHeap + DirectQuantifiedChunk("f", null, TermPerm(Ite(Eq(*(), SeqAt(S, k)), FullPerm(), NoPerm())))
    //val exhaleHeap2 = new SetBackedHeap + DirectQuantifiedChunk("f", null, TermPerm(Ite(Eq(*(), SeqAt(S, l)), FullPerm(), NoPerm())))
    val exhaleHeap1 = QuantifiedChunk("f", null, PermTimes(FullPerm(), TermPerm(MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(S, (Plus(k, IntLiteral(1)))), k))))))
    val exhaleHeap2 = QuantifiedChunk("f", null, PermTimes(FullPerm(), TermPerm(MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(S, (Plus(l, IntLiteral(1)))), l))))))

    heapManager.exhaleTest(heap, exhaleHeap1) match {
      case None => fail("exhale 1 should succeed!")
      case Some(exhaledHeap) =>
        heapManager.exhaleTest(exhaledHeap, exhaleHeap2) match {
          case None => fail("exhale 2 should succeed!")
          case Some(_) =>
        }
    }

  }

  it should "be possible to write an element where we have two times 1/2 permission (same index)" in {
    val (heapManager, decider) = createHeapManager
    emitSetPreamble(decider)
    emitMultisetPreamble(decider)
    emitSequencePreamble(decider)

    val S, T = decider.fresh(sorts.Seq(sorts.Ref))

    decider.assume(S === T)
    val k = decider.fresh("k", sorts.Int)
    decider.assume(AtLeast(k, IntLiteral(0)))
    decider.assume(Less(k, SeqLength(S)))

    val heap = new SetBackedHeap() + QuantifiedChunk("f", null, PermTimes(FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))), TermPerm(MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(S, SeqLength(S)), IntLiteral(0))))))) + QuantifiedChunk("f", null, PermTimes(FractionPerm(TermPerm(IntLiteral(1)), TermPerm(IntLiteral(2))), TermPerm(MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(T, SeqLength(T)), IntLiteral(0)))))))

    val exhaleHeap1 = QuantifiedChunk("f", null, PermTimes(FullPerm(), TermPerm(MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(S, (Plus(k, IntLiteral(1)))), k))))))

    heapManager.exhaleTest(heap, exhaleHeap1) match {
      case None => fail("exhale should succeed")
      case Some(exhaledHeap) =>
    }
  }

}