case object A
case object B

object Main {
  def main : Any => Any = {
    case x => f(x)
  }
  def f : Any => Any = {
    case A => A
    case B => f(B)
  }
}