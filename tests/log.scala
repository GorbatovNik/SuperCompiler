case object Z
case class S(n: Any)
object Main {
  def log2 : Any => Any = {
    case S(Z) => Z
    case x => S(log2(half(x)))
  }
  def half : Any => Any = {
    case S(S(x)) => S(half(x))
    case x => Z
  }
  def main : Any => Any = {
    case S(S(x)) => log2(S(S(x)))
  }
}