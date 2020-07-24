import viper.silicon.Silicon
import viper.silver.plugin.PluginAwareReporter
import viper.silver.reporter.NoopReporter
import viper.silver.testing.SMTTypeTest
import viper.silver.verifier.Verifier

class SiliconSMTTypeTest extends SMTTypeTest {
  override val verifier: Verifier = {
    val reporter = PluginAwareReporter(NoopReporter)
    val debugInfo = ("startedBy" -> "viper.silicon.SiliconSMTTypeTest") :: Nil
    new Silicon(reporter, debugInfo)
  }
}