package rpi

/**
  * The global configurations.
  */
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
    * The number of rounds after which the learner gets exhausted and gives up.
    */
  val maxRounds = 10

  /**
    * The flag indicating whether the inference should exploit silicon's framing.
    */
  val useFraming = true

  /**
    * The flag indicating whether the inference should use recursive predicates.
    */
  val useRecursion = true

  /**
    * The flag indicating whether the inference should use segmented predicates (only makes sense if recursion is
    * enabled).
    */
  val useSegments = true

  /**
    * The flag indicating whether the black box verifier used by the inference should use annotations or heuristics for
    * unfolds, folds, and related lemmas.
    *
    * Note: The heuristics implemented in the Silicon verifier are currently experimental and limited to folds and
    * unfolds.
    */
  val useAnnotations = true

  /**
    * Since Silicon is a iso-recursive verifier, we force folds in positions where a predicate needs to be
    * established, such that we only have to rely on unfold heuristics (as failing fold heuristics may yield incorrect
    * examples). This parameter regulates up to which depth we statically fold predicates.
    */
  val foldDepth = 1

  val inline = true

  val batch = true

  /**
    * The flag indicating whether silicons branching should be used to concretize values of atomic predicates.
    */
  val useBranching = true

  /**
    * The flag indicating whether parameters of inferred predicates should be renamed (mostly to test stuff).
    */
  val renameParameters = true

  val debugPrintProgram = true
  val debugPrintTemplates = true
  val debugPrintGuards = true
}

object Names {
  /**
    * The prefix used for precondition predicates.
    */
  val precondition = "P"

  /**
    * The prefix used for postcondition predicates.
    */
  val postcondition = "Q"

  /**
    * The prefix used for invariant predicates.
    */
  val invariant = "I"

  /**
    * The name used for the recursive predicate.
    */
  val recursive = "R"

  /**
    * The name used for the recursive predicate segment.
    */
  val segment = "S"

  val initAnnotation = "__init__"

  val unfoldDownAnnotation = "__unfoldDown__"

  val foldDownAnnotation = "__foldDown__"

  val foldUpAnnotation = "__foldUp__"

  val allAnnotations = Seq(
    initAnnotation,
    unfoldDownAnnotation,
    foldDownAnnotation,
    foldUpAnnotation)

  /**
    * Returns whether the given name corresponds to an annotation.
    *
    * @param name The name.
    * @return True if the name corresponds to an annotation.
    */
  def isAnnotation(name: String): Boolean =
    allAnnotations.contains(name)

  def isPredicate(name: String): Boolean =
    name == recursive || name == segment

}