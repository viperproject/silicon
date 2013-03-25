package semper
package silicon

package object common {
  def wildcardToRegex(str: String) =
    str.replace(".", "\\.").replace("?", ".?").replace("*", ".*?")
}
