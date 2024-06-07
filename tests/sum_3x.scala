case class S(x: Any)
case object Z

object Main {
  def main: Any => Any = {
    case n => sum(S(S(S(Z))), n)
  }
  def sum: (Any, Any) => Any = {
    case (x, S(n1)) => S(sum(x, n1))
    case (x, Z) => x
  }
}