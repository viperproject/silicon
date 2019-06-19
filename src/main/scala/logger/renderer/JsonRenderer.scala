package logger.renderer

trait JsonRenderer[S] extends Renderer[S, String] {
  def pair(name: String, value: String): String = {
    "\"" + name + "\":" + "\"" + escape(value) + "\""
  }

  def pairJsonObject(name: String, value: String): String = {
    "\"" + name + "\":" + value
  }

  def pair(name: String, value: Boolean): String = {
    "\"" + name + "\":" + value
  }

  def pair(name: String, value: Long): String = {
    "\"" + name + "\":" + value
  }

  def pair(name: String, value: List[Int]): String = {
    pairJsonObject(name, renderJsonArray(value))
  }

  def pairDoubleList(name: String, value: List[List[Int]]): String = {
    pairJsonObject(name, "[" + value.map(renderJsonArray).mkString(",") + "]")
  }

  def renderJsonArray(l: List[Int]): String = {
    "[" + l.mkString(",") + "]"
  }

  def escape(s: String): String = {
    var res = s
    var i = 0
    while (i < res.length()) {
      if (res(i).equals('\n')) {
        res = res.substring(0, i - 1) + "\\n" + res.substring(i + 1, res.length())
        i += 1
      } else if (res(i).equals('\\')) {
        res = res.substring(0, i - 1) + "\\\\" + res.substring(i + 1, res.length())
        i += 1
      }
      i += 1
    }
    res
  }
}
