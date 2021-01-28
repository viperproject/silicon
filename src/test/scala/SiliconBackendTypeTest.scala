import viper.silicon.Silicon
import viper.silver.plugin.PluginAwareReporter
import viper.silver.reporter.NoopReporter
import viper.silver.testing.BackendTypeTest
import viper.silver.verifier.Verifier

class SiliconBackendTypeTest extends BackendTypeTest {
  override val verifier: Verifier = {
    val reporter = PluginAwareReporter(NoopReporter)
    val debugInfo = ("startedBy" -> "viper.silicon.SiliconSMTTypeTest") :: Nil
    new Silicon(reporter, debugInfo)
  }
}