case class S(x: Any)
case object Z
case class Pair(x:Any, y:Any)

object Main {
  def main: (Any, Any) => Any = {
    case (Pair(S(x), S(y)), Pair(S(u), S(v))) => sumpair(Pair(S(x), S(y)), Pair(S(u), S(v)))
  }
  def sumpair: (Any, Any) => Any = {
    case (Pair(S(x), y), Pair(u, v)) =>  sumpair(Pair(x, y), Pair(S(u), v))
    case (Pair(x, S(y)), Pair(u, v)) =>  sumpair(Pair(x, y), Pair(u, S(v)))
    case (Pair(Z, Z), Pair(u, v)) =>  Pair(u, v)
  }
}