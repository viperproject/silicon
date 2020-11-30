package rpi

/**
  * The global configurations.
  */
object Config {
  /**
    * The flag indicating whether recursive predicates are enabled.
    */
  val enableRecursion = true

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
  val maxRounds = 5

  /**
    * The flag indicating whether the inference should exploit silicon's framing.
    */
  val useFraming = false

  /**
    * The flag indicating whether silicons branching should be used to concretize values of atomic predicates.
    */
  val useBranching = true

  /**
    * The flag indicating whether fold / unfold heuristics should be used.
    */
  val useHeuristics = false

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