package utils

case class Addr(i : Int) { //for shared node
  def isNull : Boolean = i == 0
  override def toString : String = "#" + i
  def showFW : String = (for (n <- 0 until 4 - i.toString.length) yield ' ').mkString + this
}

object Heap {
  private def ints(n : Int) : Stream[Int] = n #:: ints(n + 1)
  //hInitial = (0, [1..], [])
  def hInitial[A] : Heap[A] = Heap(0, ints(1), Map())
  val hNull : Addr = new Addr(0)
}

//heap is a triple, A is a object (heap Node)
case class Heap[A](size : Int, unused : Stream[Int], map : Map[Addr, A]) {
  def alloc(a : A) : (Heap[A], Addr) = (Heap(size + 1, unused.tail, map + (Addr(unused.head) -> a)), Addr(unused.head))
  def update(at : Addr)(a : A) : Heap[A] = Heap(size, unused, map + (at -> a))
  def free(at : Addr) : Heap[A] = Heap(size - 1, at.i #:: unused, map - at)
  def lookup(at : Addr) : A = map.getOrElse(at, throw new Exception("Cannot find node " + at + " in heap"))
  def addresses : List[Addr] = map.keySet.toList.sortBy(_ i)
}
