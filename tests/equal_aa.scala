case object Z
case object False
case object True

case class S(x: Any)

object Main {
  def main : (Any, Any) => Any = {
    case (a, b) => eq(a,a)
  }
  def eq : (Any, Any) => Any = {
    case (S(x), S(y)) => eq(x, y)
    case (S(x), Z) => False
    case (Z, S(y)) => False
    case (Z, Z) => True
  }
}