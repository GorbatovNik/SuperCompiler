case class S(x: Any)
case object Z

object Main {
  def main: (Any, Any) => Any = {
    case (S(S(Z)), x) => log2(pow(S(S(Z)), x))
  }
  def pow: (Any, Any) => Any = {
    case (x, S(y)) => mul(x, pow(x, y)) 
    case (x, Z) => S(Z)
  }
  def mul: (Any, Any) => Any = {
    case (S(x), y) => sum(y, mul(x, y))
    case (Z, y) => Z
  }
  def sum: (Any, Any) => Any = {
    case (S(x), y) => S(sum(x, y))
    case (Z, y) => y
  }
  def log2 : Any => Any = {
    case S(Z) => Z
    case x => S(log2(half(x)))
  }
  def half : Any => Any = {
    case S(S(x)) => S(half(x))
    case x => Z
  }
}