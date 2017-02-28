package template

object Evaluator extends Compile with GarbageCollect with ShowResult {
  import core._, Expr._
  import utils._

  def eval(s : TiState) : List[TiState] = {
    //        println(TiState)
    def next_sates = doAdmin(step(s))
    def rest_states = if(tiFinal(s)) Nil else eval(next_sates)
    s :: rest_states
  }

  // check the heap size
  def doAdmin(state : TiState) : TiState = state match {
    case TiState(stack, dump, heap, globals, stats) =>
//      applyToStats(tiStatIncSteps)(state)
      if (tiStatGetSteps(stats) % 25 == 24)
        garbageCollect(TiState(stack, dump, heap, globals, stats.admin(heap.size))) //gc
      else
        TiState(stack, dump, heap, globals, stats.admin(heap.size))
  }

  def tiFinal(s: TiState) : Boolean = s match {
    case TiState(stack, dump, heap, globals, stats) =>
      stack match {
        case Nil         => throw new Exception("empty stack")
        case sole_addr :: Nil => heap.lookup(sole_addr).isDataNode && dump.isEmpty
        case _           => false
      }
  }


  def step(state : TiState) : TiState = state match {
    case TiState(stack, dump, heap, globals, stats) => stack match {
      case Nil => throw new Exception("empty stack")
      case s :: Nil if heap.lookup(s).isDataNode => new TiState(dump.head, dump.tail, heap, globals, stats)
      case s :: ss => heap.lookup(s) match {
        case NMarked(s, n) => throw new Exception("found gc-marked node")
        case NNum(n) => throw new Exception("number applied as function")
        case NData(t, a) => throw new Exception("data object applied as function")
        case NAp(a, b) => heap.lookup(b) match { //apStep
          case NInd(b2) => {
            val newHeap = heap.update(s)(NAp(a, b2))
            new TiState(stack, dump, newHeap, globals, stats)
          }
          case _ => new TiState(a :: stack, dump, heap, globals, stats) //unwind rule
        }
        case NSupercomb(name, args, body) => { //scStep
          val argBindings = args.zip(getArgs(state))
          if (argBindings.length < args.length) throw new Exception("supercombinator " + name + "applied to too few arguments")
          val env = globals ++ argBindings
          val newHeap = instantiateAndUpdate(body, heap, env, stack(args.length))
          val newStack = stack.drop(args.length) //discard the arguments from the stack
          new TiState(newStack, dump, newHeap, globals, stats)
        }
        case NInd(a) => new TiState(a :: stack.tail, dump, heap, globals, stats)
        case NPrim(_, Neg) => primNeg(state)
        case NPrim(_, Add) => primArith(state)(x => y => NNum(x + y))
        case NPrim(_, Sub) => primArith(state)(x => y => NNum(x - y))
        case NPrim(_, Mul) => primArith(state)(x => y => NNum(x * y))
        case NPrim(_, Div) => primArith(state)(x => y => NNum(x / y))
        case NPrim(_, PrimConstr(n, a)) => primConstr(state, n, a)
        case NPrim(_, If) => primIf(state)
        case NPrim(_, Greater) => primArith(state)(x => y => boolify(x > y))
        case NPrim(_, GreaterEq) => primArith(state)(x => y => boolify(x >= y))
        case NPrim(_, Less) => primArith(state)(x => y => boolify(x < y))
        case NPrim(_, LessEq) => primArith(state)(x => y => boolify(x <= y))
        case NPrim(_, Eq) => primArith(state)(x => y => boolify(x == y))
        case NPrim(_, NEq) => primArith(state)(x => y => boolify(x != y))
        case NPrim(_, PrimCasePair) => primCasePair(state)
        case NPrim(_, PrimCaseList) => primCaseList(state)
        case NPrim(_, Abort) => throw new Exception("Core language abort!")
      }
    }
  }

  def boolify(b : Boolean) : Node = if (b) NData(1, Nil) else NData(2, Nil)

  //Used only with a supercombinator atop stack
  def getArgs(state : TiState) : List[Addr] = state match {
    case TiState(stack, _, heap, _, _) =>
      def getArg(addr : Addr) : Addr = {
        val NAp(fun, arg) = heap.lookup(addr)
        arg
      }
      stack.tail.map(getArg)
  }

  def instantiate(body : CoreExpr, heap : TiHeap, env : Map[String, Addr]) : (TiHeap, Addr) = body match {
    case ENum(n) => heap.alloc(NNum(n))
    case EAp(e1, e2) => {
      val (heap1, a1) = instantiate(e1, heap, env)
      val (heap2, a2) = instantiate(e2, heap1, env)
      heap2.alloc(NAp(a1, a2))
    }
    case EVar(v)             => (heap, env.getOrElse(v, throw new Exception("unidentified var " + v)))
    case EConstr(tag, arity) => heap.alloc(NPrim("Pack", PrimConstr(tag, arity)))
    case ELet(false, defs, body) => { //let
      val (newHeap, bindings) = defs.foldLeft((heap, env))(instantiateBody)
      val newEnv = env ++ bindings
      instantiate(body, newHeap, newEnv)
    }
    case ELet(true, defs, body) => { //letrec
      val heapEnv = defs.foldLeft((heap, env))(allocateBody)
      val (newHeap, newEnv) = defs.foldLeft(heapEnv)(updateBody)
      instantiate(body, newHeap, newEnv)
    }
    case ECase(e, alts) => throw new Exception("can't instantiate case exprs") //TODO
    case other => throw new Exception("can't instantiate " + other)
  }

  def instantiateBody(heapEnv : (TiHeap, Map[String, Addr]), defn : CoreDefn) : (TiHeap, Map[String, Addr]) = {
    val (oldHeap, oldEnv) = heapEnv
    val (newHeap, newAddr) = instantiate(defn._2, oldHeap, oldEnv)
    (newHeap, oldEnv + (defn._1 -> newAddr))
  }

  def allocateBody(heapEnv : (TiHeap, Map[String, Addr]), defn : CoreDefn) : (TiHeap, Map[String, Addr]) = {
    val (oldHeap, oldEnv) = heapEnv
    val (newHeap, newAddr) = oldHeap.alloc(NInd(Heap.hNull))
    (newHeap, oldEnv + (defn._1 -> newAddr))
  }

  def updateBody(heapEnv : (TiHeap, Map[String, Addr]), defn : CoreDefn) : (TiHeap, Map[String, Addr]) = {
    val (oldHeap, env) = heapEnv
    val defAddr = env.getOrElse(defn._1, throw new Exception("definition of " + defn._1 + "dissapeared before update"))
    val newHeap = instantiateAndUpdate(defn._2, oldHeap, env, defAddr)
    (newHeap, env)
  }

  //use NInd node an = #ar, to replace the root of redex
  def instantiateAndUpdate(body : CoreExpr, heap : TiHeap, env : Map[String, Addr], a : Addr) : TiHeap = body match {
    case ENum(n) => heap.update(a)(NNum(n))
    case EAp(e1, e2) => {
      val (heap1, a1) = instantiate(e1, heap, env)
      val (heap2, a2) = instantiate(e2, heap1, env)
      heap2.update(a)(NAp(a1, a2))
    }
    case EVar(v)             => heap.update(a)(NInd(env.getOrElse(v, throw new Exception("unidentified var " + v))))
    case EConstr(tag, arity) => heap.update(a)(NPrim("Pack", PrimConstr(tag, arity)))
    case ELet(false, defs, body) => {
      val (heap1, env1) = defs.foldLeft((heap, env))(instantiateBody)
      instantiateAndUpdate(body, heap1, env1, a)
    }
    case ELet(true, defs, body) => {
      val heapEnv = defs.foldLeft((heap, env))(allocateBody)
      val (heap1, env1) = defs.foldLeft(heapEnv)(updateBody)
      instantiateAndUpdate(body, heap1, env1, a)
    }
    case ECase(e, alts) => throw new Exception("can't update to case exprs")
    case other => throw new Exception("can't instantiate " + other)
  }

  def primNeg(state : TiState) : TiState = state match {
    case TiState(stack, dump, heap, globals, stats) =>
      val argAddr = getArgs(state).head
      val argNode = heap.lookup(argAddr)
      argNode match {
        case NNum(n) => {
          val newHeap = heap.update(stack(1))(NNum(-n))
          new TiState(stack.tail, dump, newHeap, globals, stats)
        }
        case _ => new TiState(argAddr :: Nil, stack.tail :: dump, heap, globals, stats)
      }
  }

  def primArith(state : TiState)(op : Int => Int => Node) : TiState = state match {
    case TiState(stack, dump, heap, globals, stats) =>
      val argAddr = getArgs(state).head
      val argNode = heap.lookup(argAddr)
      argNode match {
        case NNum(n) => {
          val argAddr2 = getArgs(state)(1)
          val argNode2 = heap.lookup(argAddr2)
          argNode2 match {
            case NNum(n2) => {
              val newHeap = heap.update(stack(2))(op(n)(n2))
              new TiState(stack.drop(2), dump, newHeap, globals, stats)
            }
            case _ => new TiState(argAddr2 :: Nil, stack.tail.tail :: dump, heap, globals, stats)
          }
        }
        case _ => new TiState(argAddr :: Nil, stack.tail :: dump, heap, globals, stats)
      }
  }

  def primIf(state : TiState) : TiState = state match {
    case TiState(stack, dump, heap, globals, stats) =>
      val argAddr = getArgs(state).head
      val argNode = heap.lookup(argAddr)
      argNode match {
        case NData(1, Nil) => {
          val newHeap = heap.update(stack(3))(NInd(getArgs(state)(1)))
          new TiState(stack.drop(3), dump, newHeap, globals, stats)
        }
        case NData(2, Nil) => {
          val newHeap = heap.update(stack(3))(NInd(getArgs(state)(2)))
          new TiState(stack.drop(3), dump, newHeap, globals, stats)
        }
        case _ => new TiState(argAddr :: Nil, stack.tail :: dump, heap, globals, stats)
      }
  }

  def primConstr(state : TiState, tag : Int, arity : Int) : TiState = state match {
    case TiState(stack, dump, heap, globals, stats) =>
      val newHeap = heap.update(stack(arity))(NData(tag, getArgs(state).take(arity)))
      new TiState(stack.drop(arity), dump, newHeap, globals, stats)
  }

  def primCasePair(state : TiState) : TiState = state match {
    case TiState(stack, dump, heap, globals, stats) =>
      val argAddr = getArgs(state).head
      val argNode = heap.lookup(argAddr)
      argNode match {
        case NData(1, List(fst, snd)) => {
          val fAddr = getArgs(state)(1)
          val (heap1, inAddr) = heap.alloc(NAp(fAddr, fst))
          val heap2 = heap1.update(stack(2))(NAp(inAddr, snd))
          new TiState(stack.drop(2), dump, heap2, globals, stats)
        }
        case _ => new TiState(argAddr :: Nil, stack.tail :: dump, heap, globals, stats)
      }
  }

  def primCaseList(state : TiState) : TiState = state match {
    case TiState(stack, dump, heap, globals, stats) =>
      val argAddr = getArgs(state).head
      val argNode = heap.lookup(argAddr)
      argNode match {
        case NData(1, Nil) => {
          val newHeap = heap.update(stack(3))(NInd(getArgs(state)(1)))
          new TiState(stack.drop(3), dump, newHeap, globals, stats)
        }
        case NData(2, List(fst, snd)) => {
          val fAddr = getArgs(state)(2)
          val (heap1, inAddr) = heap.alloc(NAp(fAddr, fst))
          val heap2 = heap1.update(stack(3))(NAp(inAddr, snd))
          new TiState(stack.drop(3), dump, heap2, globals, stats)
        }
        case _ => new TiState(argAddr :: Nil, stack.tail :: dump, heap, globals, stats)
      }
  }
}

trait ShowResult { self: Compile =>
  import utils._

  def showState(state : TiState) : String = showStack(state) + '\n'

  def showStack(state : TiState) : String = state match {
    case TiState(stack, dump, heap, globals, stats) =>
      def showStackItem(addr : Addr) : String = "   " + addr.showFW + ": " + showStackNode(heap, heap.lookup(addr))
      "Stk [\n" + stack.map(showStackItem).mkString + " ]"
  }

  def showStackNode(heap : TiHeap, node : Node) : String = node match {
    case NAp(fun, arg) => "NAp " + fun.showFW + " " + arg.showFW + " (" + showNode(heap.lookup(arg)) + ")\n"
    case node          => showNode(node) + "\n"
  }

  def showNode(node : Node) : String = node match {
    case NAp(a1, a2)            => "NAp " + a1 + " " + a2
    case NSupercomb(name, _, _) => "NSupercomb " + name
    case NNum(n)                => "NNum " + n
    case NInd(a)                => "NInd " + a
    case NPrim(n, p)            => "NPrim " + n
    case NData(t, a)            => "NData " + t + a.map(d => " " + d.toString).mkString
    case NMarked(s, n)          => throw new Exception("found gc-marked node")
  }

  def showStats(heap : TiHeap, stats: TiStats) : String = "Total number of steps = " + tiStatGetSteps(stats) + '\n' + "Final heap allocation = " + heap.size + '\n' + "Max heap allocation = " + stats.maxHeap

  def printHeap(heap : TiHeap) : String = heap.addresses.map(a => a + " = " + showStackNode(heap, heap.lookup(a))).mkString
}