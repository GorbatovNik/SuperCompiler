case class S(x: Any)
case object Z

object Main {
  def main: Any => Any = {
    case x => sum(S(x), Z)
  }
  def sum: (Any, Any) => Any = {
    case (S(x), y) => S(sum(x, S(y)))
    case (Z, y) => y
  }
}