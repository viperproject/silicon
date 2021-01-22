package rpi

/**
  * The global configurations.
  */
@deprecated
object Settings {
  /**
    * The maximal length of access paths allowed to appear in specifications.
    */
  val maxLength = 2

  /**
    * The maximal number of clauses that may be used for a guard.
    */
  val maxClauses = 1

  /**
    * The flag indicating whether tha choices for predicate arguments should be restricted to the ones appearing in the
    * samples.
    */
  val restrictChoices = true

  /**
    * The folding delta: Since Silicon is a iso-recursive verifier, we force additional folds in positions where
    * a predicate needs to be established, such that we only have to rely on unfold heuristics (as failing fold
    * heuristics may yield incorrect samples). This parameter regulates up to which depth we statically fold
    * predicates.
    */
  val foldDelta: Int = 1

  /**
    * The flag indicating whether specification predicates are inlined.
    */
  val inline = true

  /**
    * The flag indicating whether the checks of a single top-level iteration are processed in a single batch.
    */
  val batch = false

  /**
    * The flag indicating whether silicons branching should be used to concretie values of atomic predicates.
    */
  val useBranching = true

  /**
    * The flag indicating whether parameters of inferred predicates should be renamed (mostly to test stuff).
    */
  val renameParameters = false
}

object Names {
  /**
    * The prefix used for precondition predicates.
    */
  val precondition = "pre"

  /**
    * The prefix used for postcondition predicates.
    */
  val postcondition = "post"

  /**
    * The prefix used for invariant predicates.
    */
  val invariant = "inv"

  /**
    * The name used for the recursive predicate.
    */
  val recursive = "P"

  val appendLemma = "append_lemma"

  val downAnnotation = "__down__"

  val upAnnotation = "__up__"

  val allAnnotations = Seq(
    downAnnotation,
    upAnnotation)

  /**
    * Returns whether the given name corresponds to an annotation.
    *
    * @param name The name.
    * @return True if the name corresponds to an annotation.
    */
  def isAnnotation(name: String): Boolean =
    allAnnotations.contains(name)

  def isRecursive(name: String): Boolean =
    name == recursive
}