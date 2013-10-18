package semper
package silicon
package heap


import interfaces.{VerificationResult}
import semper.silicon.interfaces.state.{State, PathConditions, Heap, Store}
import semper.silicon.interfaces.reporting.TraceView
import semper.silicon.state.terms.Term
import semper.silicon.state.DirectChunk
import semper.silicon.ast.Field


trait DefaultHeapManager[H <: Heap[H]] {

  def setValue(inHeap:H, ofReceiver:Term, withField:Field, toValue:Term,  Q: H => VerificationResult) :VerificationResult {

  }

}
