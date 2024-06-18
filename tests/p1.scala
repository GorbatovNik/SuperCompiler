case object A
case object B
case object Z
case class S(x: Any)

object Main {
  def main : Any => Any = {
    case x => g(x)
  }
  def g : Any => Any = {
    case Z => S(Z)
    case S(S(S(x))) => g(g(x)) 
    case x => f(g(Z))
  }
  def f : Any => Any = {
    case x => S(x)
  }
}