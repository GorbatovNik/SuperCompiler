case class S(x: Any)
case class Cons(x: Any, y: Any)
case object Z
case object Nil_

object Main {
  def main: (Any, Any) => Any = {
    case (Cons(Z, Nil_), S(inc), S(S(S(S(S(Z)))))) => f(Cons(Z, Nil_), S(inc), S(S(S(S(S(Z)))))) 
  }
  def f: (Any, Any, Any) => Any = {
    case (xs, inc, Z) => xs
    case (Cons(a, xs), inc, S(x)) => f(Cons(sum(a, inc), Cons(a, xs)), inc, x)
  }
  def sum: (Any, Any) => Any = {
    case (x, S(n1)) => S(sum(x, n1))
    case (x, Z) => x
  }
}