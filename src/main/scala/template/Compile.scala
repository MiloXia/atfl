package template

import core.Expr.{ CoreProgram, CoreScDefn, preludeDefs }
import core.ExprParser.{ parse, parseSC }
import utils.Addr
import utils.Heap
import utils.Heap.hInitial
import Primitive.primitives
import core.EConstr


trait Compile {
  type TiStack = List[Addr]
  type TiHeap = Heap[Node]
  type TiGlobals = Map[String, Addr]
  type TiDump = List[TiStack]

  case class TiState(stack : TiStack, dump : TiDump, heap : TiHeap, globals : TiGlobals, stats : TiStats)

  case class TiStats(steps : Int, maxHeap : Int) {
    def admin(heapSize : Int) : TiStats = TiStats(steps + 1, Math.max(heapSize, maxHeap))
  }
  def tiStatInitial: TiStats = TiStats(0, 0)
  def tiStatIncSteps(s : TiStats): TiStats = TiStats(s.steps + 1, s.maxHeap)
  def tiStatGetSteps(s : TiStats): Int = s.steps
  def applyToStats(stats_fun : TiStats => TiStats)(s: TiState) : TiState = s match {
    case TiState(stack, dump, heap, sc_defs, stats) => TiState(stack, dump, heap, sc_defs, stats_fun(stats))
  }
  val maxHeap : Int = 0 //TODO
//  def admin(s : TiStats, heapSize : Int) : TiStats = new TiStats(tiStatGetSteps(s) + 1, Math.max(heapSize, maxHeap))

  val initialTiDump = Nil

//  def run(prog : String) : String = showResults(compile(parse(prog)).eval)

  def compile(prog : CoreProgram) : TiState = {
    val scdefs = prog ++ preludeDefs ++ extraPreludeDefs
    val (initialHeap, globals) = buildInitialHeap(scdefs)
    val addressOfMain = globals.getOrElse("main", throw new Exception("main is not defined"))
    val initialStack = List(addressOfMain)
    new TiState(initialStack, initialTiDump, initialHeap, globals, tiStatInitial)
  }

  def buildInitialHeap(prog : CoreProgram) : (TiHeap, TiGlobals) = innerBIH(prog, hInitial)
  def innerBIH(prog : CoreProgram, heap : TiHeap) : (TiHeap, TiGlobals) = prog match {
    case Nil => innerBIHPrim(primitives, heap)
    case x :: xs => {
      val (acc1, xp) = allocateSc(heap, x)
      val (acc2, xsp) = innerBIH(xs, acc1)
      (acc2, xsp + xp)
    }
  }
  def innerBIHPrim(prims : List[(String, Primitive)], heap : TiHeap) : (TiHeap, TiGlobals) = prims match {
    case Nil => (heap, Map())
    case x :: xs => {
      val (acc1, xp) = allocatePrim(heap, x)
      val (acc2, xsp) = innerBIHPrim(xs, acc1)
      (acc2, xsp + xp)
    }
  }

  def allocateSc(heap : TiHeap, sc : CoreScDefn) : (TiHeap, (String, Addr)) = {
    val (heapp, addr) = heap.alloc(NSupercomb(sc._1, sc._2, sc._3))
    (heapp, (sc._1, addr))
  }

  def allocatePrim(heap : TiHeap, prim : (String, Primitive)) : (TiHeap, (String, Addr)) = {
    val (heapp, addr) = heap.alloc(NPrim(prim._1, prim._2))
    (heapp, (prim._1, addr))
  }

//  def showResults(trace : List[TiState]) : String =
//  //    iLayn(trace.map(x => iStr(x.showState))).display +
//    trace.last.showStack + trace.last.showStats

  val extraPreludeDefs : List[CoreScDefn] = List(
    ("True", Nil, EConstr(1, 0)),
    ("False", Nil, EConstr(2, 0)),
    ("MkPair", Nil, EConstr(1, 2)),
    ("Nil", Nil, EConstr(1, 0)),
    ("Cons", Nil, EConstr(2, 2)),
    parseSC("and x y = if x y False"),
    parseSC("or x y = if x True y"),
    parseSC("not x = if x False True"),
    parseSC("xor x y = if x (not y) y"),
    parseSC("fst p = casePair p K"),
    parseSC("snd p = casePair p K1"),
    parseSC("head l = caseList l abort K"),
    parseSC("tail l = caseList l abort K1")
  )
}
