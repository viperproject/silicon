package semper
package silicon
package ast

object expressions {
  /** Erases all ghost operations such as unfolding from the given expression `e`.
    * For example (let A, B and C be free of ghost operations, let P be a predicates,
    * and let W be a wand):
    *
    *     A && unfolding P in B && applying W in C
    *
    * will be transformed into
    *
    *     A && B && C
    *
    * If `e` itself is not a ghost operation, then the resulting expression
    * will be an instance of the class `e` is an instance of. That is, the
    * result can safely be casted to `e`'s type.
    *
    * @param e An expression to erase all ghost operations from.
    * @return The ghost-operations-free version of `e`.
    */
  def eraseGhostOperations(e: ast.Expression): ast.Expression =
    /* We use the post-transformer instead of the pre-transformer in order to
     * perform bottom-up transformation. With a top-down transformer we could
     * not simply replace ghost operations with their bodies, because these
     * can contain ghost operations themselves, to which the transformer
     * would not be applied (per se).
     */
    e.transform()(post = {
      case u: ast.Unfolding if !u.isPure => u.body
      case gop: ast.GhostOperation if !gop.isInstanceOf[ast.Unfolding] => gop.body
    })
}
