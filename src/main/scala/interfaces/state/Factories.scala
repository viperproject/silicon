package semper
package silicon
package interfaces.state

import scala.language.implicitConversions
import silicon.state.terms.Term

object factoryUtils {
	trait Ø
	object Ø extends Ø
}

trait StoreFactory[ST <: Store[ST]] {
	implicit def ØToEmptyStore(ø: factoryUtils.Ø): ST = Γ()

	def Γ(): ST
	def Γ(store: Map[ast.Variable, Term]): ST
	def Γ(pair: (ast.Variable, Term)): ST
	def Γ(pairs: Iterable[(ast.Variable, Term)]): ST
}

trait PathConditionsFactory[PC <: PathConditions[PC]] {
	implicit def ØToEmptyPathConditions(ø: factoryUtils.Ø): PC = Π()

	def Π(): PC
	def Π(terms: Term): PC
	def Π(terms: Set[Term]): PC
}

trait HeapFactory[H <: Heap[H]] {
	implicit def ØToEmptyHeap(ø: factoryUtils.Ø): H = H()

	def H(): H
	def H(h: H): H
	def H(chunks: Iterable[Chunk]): H
}

trait StateFactory[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
		extends StoreFactory[ST] with HeapFactory[H] {

	implicit def ØToEmptyState(ø: factoryUtils.Ø): S = Σ()

	def Σ(): S
	def Σ(γ: ST, h: H, g: H): S
}
