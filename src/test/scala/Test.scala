import template.Evaluator
import typecheck.hindley_milner.{HindleyMilner, AST_Transform, SyntaxNode}

object Test {
  import core._, PrettyPrinter._

  def main(args: Array[String]): Unit = {
    val mapTest = pprProgram(Expr.mapTest)
    println(mapTest)

    val progStr =
      """
        |f = 3 ;
        |g x y = let z = x in z ;
        |h x = case (let y = x in y) of
        |<1> -> 2 ;
        |<2> -> 5
      """.stripMargin
    val prog = ExprParser.parse(progStr)
    println(pprProgram(prog))

    val progStr2 =
      """
        |pair x y f = f x y ;
        |fst p = p K ;
        |snd p = p K1 ;
        |f x y = letrec
        |          a = pair x b ;
        |          b = pair y a
        |        in
        |        fst (snd (snd (snd a))) ;
        |main = f 3 4
      """.stripMargin
    val prog2 = ExprParser.parse(progStr2)
    val l = Evaluator.eval(Evaluator.compile(prog2))
    println(Evaluator.showState(l.last))
    val exprStr =
      """
        | let g = (\ f. 5) in g g
      """.stripMargin

    val expr = ExprParser.parseExpr(exprStr)
    val exprNodes = AST_Transform.tranExpr(expr)
    val typeStrs = HindleyMilner.typeCheck(exprNodes :: Nil)
    println("res1: " + SyntaxNode.nakedString(exprNodes) + typeStrs.head)
  }
}
