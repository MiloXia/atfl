package core

//data Expr a
// = EVar Name                     -- Variables
// | ENum Int                      -- Numbers
// | EConstr Int Int               -- Constructor tag arity
// | EAp (Expr a) (Expr a)         -- Applications
// | ELet                          -- Let(rec) expressions
//      IsRec                      -- boolean with True = recursive,
//      [(a, Expr a)]              -- Definitions
//      (Expr a)                   -- Body of let(rec)
// | ECase                         -- Case expression
//      (Expr a)                   -- Expression to scrutinise
//      [Alter a]                  -- Alternatives
// | ELam [a] (Expr a)             -- Lambda abstractions

import Expr._
//AST
sealed trait Expr[+A]
case class EVar(n : Name) extends Expr[Nothing]
case class ENum(i : Int) extends Expr[Nothing]
case class EConstr(tag : Int, arity : Int) extends Expr[Nothing]
case class EAp[A](rator : Expr[A], rand : Expr[A]) extends Expr[A]
case class ELet[A](isRec : Boolean, defns : List[Defn[A]], body : Expr[A]) extends Expr[A]
case class ECase[A](expr : Expr[A], alts : List[Alter[A]]) extends Expr[A]
case class ELam[A](vars : List[A], body : Expr[A]) extends Expr[A]

object Expr {
  type Name = String
  type Defn[A] = (A, Expr[A])
  type Alter[A] = (Int, List[A], Expr[A])
  type Program[A] = List[ScDefn[A]]
  type ScDefn[A] = (Name, List[A], Expr[A])

  type CoreExpr = Expr[Name]
  type CoreDefn = Defn[Name]
  type CoreAlt = Alter[Name]
  type CoreProgram = Program[Name]
  type CoreScDefn = ScDefn[Name]

  def bindersOf[A](defns : List[Defn[A]]) : List[A] = for ((name, rhs) <- defns) yield name
  def rhsOf[A](defns : List[Defn[A]]) : List[Expr[A]] = for ((name, rhs) <- defns) yield rhs
  def isAtomicExpr[A](expr : Expr[A]) : Boolean = expr match {
    case EVar(n) => true
    case ENum(i) => true
    case _       => false
  }

  val preludeDefs : CoreProgram = List(
    ("I", List("x"), EVar("x")),
    ("K", List("x", "y"), EVar("x")),
    ("K1", List("x", "y"), EVar("y")),
    ("S", List("f", "g", "x"), EAp(EAp(EVar("f"), EVar("x")), EAp(EVar("g"), EVar("x")))),
    ("compose", List("f", "g", "x"), EAp(EVar("f"), EAp(EVar("g"), EVar("x")))),
    ("twice", List("f"), EAp(EAp(EVar("compose"), EVar("f")), EVar("f")))
  )

  val mapTest : CoreProgram = List(
    ("map", List("f"), ELam(List("x"), ECase(EVar("x"), List((1, Nil, EConstr(1, 0)),
      (2, List("xs"), EAp(EAp(EConstr(2, 2), EAp(EVar("f"), EVar("x"))), EAp(EAp(EVar("map"), EVar("f")), EVar("xs")))))))),
    ("fold", List("f", "k"), ELet(true, List(("m", ELam(List("x"), ECase(EVar("x"), List((1, Nil, EConstr(1, 0)),
      (2, List("xs"), EAp(EAp(EConstr(2, 2), EAp(EVar("f"), EVar("x"))), EAp(EAp(EVar("map"), EVar("f")), EVar("xs"))))))))),
      EAp(EVar("map"), EVar("k")))))
}