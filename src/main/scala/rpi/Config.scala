package rpi

/**
  * The global configurations.
  */
object Config {
  /**
    * The maximal number of clauses that may be used for a guard.
    */
  val maxClauses = 1

  /**
    * The maximal length of access paths allowed to appear in specifications.
    */
  val maxLength = 2

  /**
    * The number of rounds after which the learner gets exhausted and gives up.
    */
  val maxRounds = 4

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
}
