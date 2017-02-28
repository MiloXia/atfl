package template


trait GarbageCollect { slef : Compile =>
  import utils._

  def garbageCollect(state : TiState) : TiState = state match {
    case TiState(stack, dump, heap, globals, stats) =>
      val (stackHeap, newStack) = markFromList(heap, stack)
      val (dumpHeap, newDump) = markFromDump(dump, stackHeap)
      val (globalsHeap, newGlobals) = markFromGlobals(globals, dumpHeap)
      val cleanHeap = scanHeap(globalsHeap)
      new TiState(newStack, newDump, cleanHeap, newGlobals, stats)
  }

  def markFromGlobals(globals : TiGlobals, heap : TiHeap) : (TiHeap, Map[String, Addr]) = markFromGlobals(heap, globals, globals.keySet.toList)
  def markFromGlobals(heap : TiHeap, as : Map[String, Addr], unmarked : List[String]) : (TiHeap, Map[String, Addr]) =
    unmarked match {
      case Nil => (heap, as)
      case g :: gs => {
        val (newHeap, a) = markFrom(heap, as(g))
        markFromGlobals(newHeap, as + (g -> a), gs)
      }
    }

  def markFromDump(dump : TiDump, heap : TiHeap) : (TiHeap, List[List[Addr]]) = markFromDump(heap, dump, Nil)
  def markFromDump(heap : TiHeap, as : List[List[Addr]], newAs : List[List[Addr]]) : (TiHeap, List[List[Addr]]) =
    as match {
      case Nil => (heap, newAs.reverse)
      case a :: as2 => {
        val (newHeap, a2) = markFromList(heap, a)
        markFromDump(newHeap, as2, a2 :: newAs)
      }
    }

  def markFromList(heap : TiHeap, as : List[Addr]) : (TiHeap, List[Addr]) = markFromList(heap, as, Nil)
  def markFromList(heap : TiHeap, as : List[Addr], newAs : List[Addr]) : (TiHeap, List[Addr]) =
    as match {
      case Nil => (heap, newAs.reverse)
      case a :: as2 => {
        val (newHeap, a2) = markFrom(heap, a)
        markFromList(newHeap, as2, a2 :: newAs)
      }
    }

  // take an address and a heap, mark all the nodes accessible from the address, and
  // return a new heap together with a new address which should be used instead of the old one
  def markFrom(heap : TiHeap, a : Addr) : (TiHeap, Addr) = markReversingPointers(a, Heap.hNull, heap)
  def markReversingPointers(a : Addr, b : Addr, heap : TiHeap) : (TiHeap, Addr) =
    heap.lookup(a) match {
      case NAp(a1, a2)                  => markReversingPointers(a1, a, heap.update(a)(NMarked(Visit(1), NAp(b, a2))))
      case NInd(a1)                     => markReversingPointers(a1, b, heap) //short-circuit
      case NData(t, as :: ass)          => markReversingPointers(as, a, heap.update(a)(NMarked(Visit(1), NData(t, b :: ass))))
      case NMarked(Done, n) if b.isNull => (heap, a)
      case NMarked(_, n) => heap.lookup(b) match {
        case NMarked(Visit(1), NAp(b2, a2)) => markReversingPointers(a2, b, heap.update(b)(NMarked(Visit(2), NAp(a, b2))))
        case NMarked(Visit(2), NAp(a1, b2)) => markReversingPointers(b, b2, heap.update(b)(NMarked(Done, NAp(a1, a))))
        case NMarked(Visit(n), NData(t, as)) =>
          if (n == as.length)
            markReversingPointers(b, as.last, heap.update(b)(NMarked(Done, NData(t, as.init ++ List(a)))))
          else
            markReversingPointers(as(n), b, heap.update(b)(NMarked(Visit(n + 1), NData(t, as.take(n - 1) ++ List(a) ++ as.drop(n)))))
        case _ => throw new Exception("garbage collector in impossible state")
      }
      case node => markReversingPointers(a, b, heap.update(a)(NMarked(Done, node))) //Nullary data, nums, scs, prims
    }

  def scanHeap(heap : TiHeap) : TiHeap = heap.addresses.foldLeft(heap)(freeGarbage)

  def freeGarbage(heap : TiHeap, a : Addr) : TiHeap =
    heap.lookup(a) match {
      case NMarked(s, n) => heap.update(a)(n)
      case _             => heap.free(a)
    }
}
