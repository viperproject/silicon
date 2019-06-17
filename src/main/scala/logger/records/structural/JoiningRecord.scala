package logger.records.structural

class JoiningRecord(branchingRef: BranchingRecord) extends StructuralRecord {
  val branchingRefId: Int = branchingRef.id
}
