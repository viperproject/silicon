package logger.records.data

import viper.silicon.state.terms.Term

trait MemberRecord extends DataRecord {
  var lastFailedProverQuery: Option[Term] = None
}
