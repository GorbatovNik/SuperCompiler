case object A
case object B
case object C
case object Nil_
case class Cons(head: Any, tail: Any)
 
object Main {
  def fab : Any => Any = {
    case Cons(A, xs) => Cons(B, fab(xs))
    case Cons(x, xs) => Cons(x, fab(xs))
    case Nil_ => Nil_
  }
 
  def fbc : Any => Any = {
    case Cons(B, xs) => Cons(C, fbc(xs))
    case Cons(x, xs) => Cons(x, fbc(xs))
    case Nil_ => Nil_
  }
 
  def main : Any => Any = {
    case xs => fbc(fab(Cons(A,xs)))
  }
}