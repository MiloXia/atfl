package typecheck.hindley_milner

import core._
import core.Expr._

object AST_Transform {
  def tranProgram(prog : CoreProgram) : List[SyntaxNode] = prog.map(sc => tranScDefn(sc))

  def tranScDefn(scdefn : CoreScDefn) : SyntaxNode = ??? //TODO

  def tranExpr(expr : CoreExpr) : SyntaxNode = expr match {
    case ENum(n)     => Ident(n.toString)
    case EVar(v)     => Ident(v)
    case EAp(e1, e2) => Apply(tranExpr(e1), tranExpr(e2))
    case ELet(isRec, defns, e) =>
      if (defns.size > 1) throw new Exception("not support mult 'defns' now -_-!")
      else {
        if (!isRec) Let(defns.head._1, tranExpr(defns.head._2), tranExpr(e))
        else Letrec(defns.head._1, tranExpr(defns.head._2), tranExpr(e))
      }
    case ELam(vs, body) =>
      if (vs.size > 1) throw new Exception("not support mult args now -_-!")
      Lambda(vs.head, tranExpr(body))
    case ECase(expr, alts) => throw new Exception("not support 'case' now -_-!")
    case EConstr(tag, arity) => throw new Exception("not support ADT now -_-!")
  }
}
