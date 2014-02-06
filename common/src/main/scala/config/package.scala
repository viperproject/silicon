package semper
package silicon
package common

package object config {
  def wildcardToRegex(str: String) =
    str.replace(".", "\\.")
       .replace("?", ".?")
       .replace("*", ".*?")
       .replace("$", "\\$")
}
