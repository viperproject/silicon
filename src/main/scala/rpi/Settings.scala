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
    * TODO: Implement or remove.
    */
  val useAnnotations = true

  val foldDepth = 1

  val batch = false

  /**
    * The flag indicating whether silicons branching should be used to concretize values of atomic predicates.
    */
  val useBranching = true

  /**
    * The flag indicating whether parameters of inferred predicates should be renamed (mostly to test stuff).
    */
  val renameParameters = false

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

  /**
    * The name of the fold annotation.
    */
  val foldAnnotation = "__fold__"

  /**
    * The name of the unfold annotation.
    */
  val unfoldAnnotation = "__unfold__"

  /**
    * Returns whether the given name corresponds to an annotation.
    *
    * @param name The name.
    * @return True if the name corresponds to an annotation.
    */
  def isAnnotation(name: String): Boolean =
    name == foldAnnotation || name == unfoldAnnotation
}