package typecheck.hindley_milner

import core.Expr

/*
 * based on the paper by Luca Cardelli at
 * http://lucacardelli.name/Papers/BasicTypechecking.pdf
 */

sealed trait SyntaxNode
case class Lambda(v: String, body: SyntaxNode) extends SyntaxNode //ELam
case class Ident(name: String) extends SyntaxNode //Evar
case class Apply(fn: SyntaxNode, arg: SyntaxNode) extends SyntaxNode //EAp
case class Let(v: String, defn: SyntaxNode, body: SyntaxNode) extends SyntaxNode //ELet
case class Letrec(v: String, defn: SyntaxNode, body: SyntaxNode) extends SyntaxNode //ELet

object SyntaxNode {

  def string(ast: SyntaxNode): String = {
    if (ast.isInstanceOf[Ident])
      nakedString(ast)
    else
      "("+nakedString(ast)+")"
  }

  def nakedString(ast: SyntaxNode) = ast match {
    case i: Ident => i.name
    case l: Lambda => "fn "+l.v+" ⇒ "+string(l.body)
    case f: Apply => string(f.fn)+" "+string(f.arg)
    case l: Let => "let "+l.v+" = "+string(l.defn)+" in "+string(l.body)
    case l: Letrec => "letrec "+l.v+" = "+string(l.defn)+" in "+string(l.body)
  }
}

class TypeError(msg: String) extends Exception(msg)
class ParseError(msg: String) extends Exception(msg)


object TypeSystem {

  type Env = Map[String, Type]

  abstract class Type
  // ## Type variable
  //
  // A type variable represents an parameter with an unknown type or any
  // polymorphic type. For example:
  //
  //     fun id x = x
  //
  // Here, `id` has the polymorphic type `'a -> 'a`.
  case class Variable(id: Int) extends Type {
    var instance: Option[Type] = None
    lazy val name = nextUniqueName
  }
  // ## Base type
  case class Oper(name: String, args: Seq[Type]) extends Type
  def Function(from: Type, to: Type) = Oper("→", Array(from, to))
  val Integer = Oper("int", Seq())
  val Bool = Oper("bool", Seq())

  var _nextVariableName = 'α';
  def nextUniqueName = {
    val result = _nextVariableName
    _nextVariableName = (_nextVariableName.toInt + 1).toChar
    result.toString
  }
  var _nextVariableId = 0
  def newVariable: Variable = {
    val result = _nextVariableId
    _nextVariableId += 1
    Variable(result)
  }

  def string(t: Type): String = t match {
    // Type variables should look like `'a`. If the variable has an instance, that
    // should be used for the string instead.
    case v: Variable => v.instance match {
      case Some(i) => string(i)
      case None => v.name
    }
    case Oper(name, args) => {
      if (args.length == 0) //single mono
        name
      else if (args.length == 2) //Function
        "("+string(args(0))+" "+name+" "+string(args(1))+")"
      else
        args.mkString(name + " ", " ", "")
    }
  }

  def string2(t: Type): String = t match { //for debug info
    case v: Variable => v.instance match {
      case Some(i) => v.name // + ".inst = " + string2(i)
      case None => v.name
    }
    case Oper(name, args) => {
      if (args.length == 0) //single mono
        name
      else if (args.length == 2) //Function
        "("+string2(args(0))+" "+name+" "+string2(args(1))+")"
      else
        args.mkString(name + " ", " ", "")
    }
  }

  def printlnNongen(nongen: Set[Variable]) {
    print("nongen: {")
    nongen.foreach(x => print(x.name + " "))
    println(" }")
  }


  def analyse(ast: SyntaxNode, env: Env): Type = analyse(ast, env, Set.empty)
  def analyse(ast: SyntaxNode, env: Env, nongen: Set[Variable]): Type = ast match {
    // #### Identifier
    //
    // Creates a `fresh` copy of a type if the name is found in an
    // enviroment, otherwise throws an error.
    case Ident(name) => {
      val identtype = gettype(name, env, nongen)
      println(SyntaxNode.string(ast) + " : "+ string2(identtype))
      HindleyMilner.printlnEnv(env)
      printlnNongen(nongen)
      identtype
    }
    // #### Function call
    //
    // Ensures that all argument types `unify` with the defined function and
    // returns the function's result type.
    case Apply(fn, arg) => {
      val funtype = analyse(fn, env, nongen)
      val argtype = analyse(arg, env, nongen)
      val resulttype = newVariable //not add to nongen
      unify(Function(argtype, resulttype), funtype)
      println(SyntaxNode.string(ast) + " : "+ string2(resulttype))
      HindleyMilner.printlnEnv(env)
      printlnNongen(nongen)
      resulttype
    }
    // #### Function definition
    //
    // Assigns a type variable to each typeless argument and return type.
    //
    // Each typeless argument also gets added to the non-generic scope
    // array. The `fresh` function can then return the existing type from
    // the scope.
    //
    // Assigns the function's type in the environment and returns it.
    case Lambda(arg, body) => {
      val argtype = newVariable
      val resulttype = analyse(body,
        env + (arg -> argtype),
        nongen + argtype)
      val ftype = Function(argtype, resulttype)
      println(SyntaxNode.string(ast) + " : "+ string2(ftype))
      HindleyMilner.printlnEnv(env + (arg -> argtype))
      printlnNongen(nongen + argtype)
      ftype
    }
    // #### Let binding
    //
    // Infer the value's type, assigns it in the environment and returns it.
    case Let(v, defn, body) => {
      val defntype = analyse(defn, env, nongen)
      val newenv = env + (v -> defntype)
      val lettype = analyse(body, newenv, nongen)
      //defntype lettype 是分开分析的，env和nongen就此分开
      println(SyntaxNode.string(ast) + " : "+ string2(lettype))
      HindleyMilner.printlnEnv(newenv)
      printlnNongen(nongen)
      lettype
    }

    case Letrec(v, defn, body) => {
      val newtype = newVariable
      val newenv = env + (v -> newtype)
      val defntype = analyse(defn, newenv, nongen + newtype)
      unify(newtype, defntype)
      analyse(body, newenv, nongen)
    }
  }

  def gettype(name: String, env: Env, nongen: Set[Variable]): Type = {
    if (env.contains(name))
      fresh(env(name), nongen)

    else if (isIntegerLiteral(name))
      Integer

    else
      throw new ParseError("Undefined symbol "+name)
  }

  // ### Fresh type
  //
  // Getting a "fresh" type will create a recursive copy. When a generic type
  // variable is encountered, a new variable is generated and substituted in.
  //
  // *Note*: Copied types are instantiated through the BaseType constructor, this
  // means `instanceof` can't be used for determining a subtype.
  //
  // A fresh type is only returned when an identifier is found during analysis.
  // See `analyse` for some context.

  def fresh(t: Type, nongen: Set[Variable]) = {
    import scala.collection.mutable
    val mappings = new mutable.HashMap[Variable, Variable]
    def freshrec(tp: Type): Type = {
      prune(tp) match {
        case v: Variable =>
          if (isgeneric(v, nongen))
            mappings.getOrElseUpdate(v, newVariable)
          else
            v

        case Oper(name, args) =>
          Oper(name, args.map(freshrec(_)))
      }
    }

    freshrec(t)
  }


  // ### Unification
  //
  // This is the process of finding a type that satisfies some given constraints.
  // In this system, unification will try to satisfy that either:
  //
  // 1. `t1` and `t2` are equal type variables
  // 2. `t1` and `t2` are equal types
  //
  // In case #1, if `t1` is a type variable and `t2` is not currently equal,
  // unification will set `t1` to have an instance of `t2`. When `t1` is pruned,
  // it will unchain to a type without an instance.
  //
  // In case #2, do a deep unification on the type, using recursion.
  //
  // If neither constraint can be met, the process will throw an error message.
  def unify(t1: Type, t2: Type) {
    val type1 = prune(t1)
    val type2 = prune(t2)
    (type1, type2) match {
      //instantiate a variable
      case (a: Variable, b) => if (a != b) {
        if (occursintype(a, b)) //a must not be occurs in type b
          throw new TypeError("recursive unification")
        a.instance = Some(b)
        println(s"${a.name} = ${string2(b)}")
      }
      case (a: Oper, b: Variable) => unify(b, a)
      case (a: Oper, b: Oper) => {
        if (a.name != b.name ||
          a.args.length != b.args.length) throw new TypeError("Type mismatch: "+string(a)+"≠"+string(b))

        for(i <- 0 until a.args.length)
          unify(a.args(i), b.args(i))
      }
    }
  }

  // ### Prune
  // Returns the currently defining instance of t.
  // As a side effect, collapses the list of type instances.
  def prune(t: Type): Type = t match {
    case v: Variable if v.instance.isDefined => {
      var inst = prune(v.instance.get)
      v.instance = Some(inst)
      inst
    }
    case _ => t
  }

  // Note: must be called with v 'pre-pruned'
  def isgeneric(v: Variable, nongen: Set[Variable]) = !(occursin(v, nongen))

  // Note: must be called with v 'pre-pruned'
  def occursintype(v: Variable, type2: Type): Boolean = {
    prune(type2) match {
      case `v` => true
      case Oper(name, args) => occursin(v, args)
      case _ => false
    }
  }

  // ### Occurs check
  //
  // These functions check whether the type `t2` is equal to or contained within
  // the type `t1`. Used for checking recursive definitions in `unify` and
  // checking if a variable is non-generic in `fresh`.
  def occursin(t: Variable, list: Iterable[Type]) =
    list exists (t2 => occursintype(t, t2))

  val checkDigits = "^(\\d+)$".r
  def isIntegerLiteral(name: String) = checkDigits.findFirstIn(name).isDefined

}

object HindleyMilner {

  def main(args: Array[String]){
    Console.setOut(new java.io.PrintStream(Console.out, true, "utf-8"))

    val var1 = TypeSystem.newVariable
    val var2 = TypeSystem.newVariable
    val pairtype = TypeSystem.Oper("×", Array(var1, var2))

    val var3 = TypeSystem.newVariable

    val myenv: TypeSystem.Env = Map.empty ++ Array(
      "pair" -> TypeSystem.Function(var1, TypeSystem.Function(var2, pairtype)),
      "true" -> TypeSystem.Bool,
      "cond" -> TypeSystem.Function(TypeSystem.Bool, TypeSystem.Function(var3, TypeSystem.Function(var3, var3))),
      "zero" -> TypeSystem.Function(TypeSystem.Integer, TypeSystem.Bool),
      "pred" -> TypeSystem.Function(TypeSystem.Integer, TypeSystem.Integer),
      "times"-> TypeSystem.Function(TypeSystem.Integer, TypeSystem.Function(TypeSystem.Integer, TypeSystem.Integer))
    )


    val pair = Apply(Apply(Ident("pair"), Apply(Ident("f"), Ident("4"))), Apply(Ident("f"), Ident("true")))
    val examples = Array[SyntaxNode](
      // factorial

      // Letrec("factorial", // letrec factorial =
      // 	Lambda("n",    // fn n =>
      // 		Apply(
      // 			Apply(   // cond (zero n) 1
      // 				Apply(Ident("cond"),     // cond (zero n)
      // 					Apply(Ident("zero"), Ident("n"))),
      // 				Ident("1")),
      // 			Apply(    // times n
      // 				Apply(Ident("times"), Ident("n")),
      // 				Apply(Ident("factorial"),
      // 					Apply(Ident("pred"), Ident("n")))
      // 			)
      // 		)
      // 	),      // in
      // 	Apply(Ident("factorial"), Ident("5"))
      // ),

      // Should fail:
      // fn x => (pair(x(3) (x(true)))

      // Lambda("x",
      // 	Apply(
      // 		Apply(Ident("pair"),
      // 			Apply(Ident("x"), Ident("3"))),
      // 		Apply(Ident("x"), Ident("true")))),

      // pair(f(3), f(true))
      // Apply(
      // 	Apply(Ident("pair"), Apply(Ident("f"), Ident("4"))),
      // 	Apply(Ident("f"), Ident("true"))),


      // letrec f = (fn x => x) in ((pair (f 4)) (f true))
      // Let("f", Lambda("x", Ident("x")), pair),

      // fn f => f f (fail)
      // Lambda("f", Apply(Ident("f"), Ident("f"))),

      // let g = fn f => 5 in g g

      // Let("g",
      //	Lambda("f", Ident("5")),
      //	Apply(Ident("g"), Ident("g"))),

      // example that demonstrates generic and non-generic variables:
      // fn g => let f = fn x => g in pair (f 3, f true)
      Lambda("g",
        Let("f",
          Lambda("x", Ident("g")),
          Apply(
            Apply(Ident("pair"),
              Apply(Ident("f"), Ident("3"))
            ),
            Apply(Ident("f"), Ident("true"))))) //,

      // Function composition
      // fn f (fn g (fn arg (f g arg)))
      //Lambda("f", Lambda("g", Lambda("arg", Apply(Ident("g"), Apply(Ident("f"), Ident("arg"))))))
    )
    for(eg <- examples){
      tryexp(myenv, eg)
    }
  }

  def typeCheck(asts: List[SyntaxNode]) = {
    val var1 = TypeSystem.newVariable
    val var2 = TypeSystem.newVariable
    val pairtype = TypeSystem.Oper("×", Array(var1, var2))

    val var3 = TypeSystem.newVariable

    val myenv: TypeSystem.Env = Map.empty ++ Array(
      "pair" -> TypeSystem.Function(var1, TypeSystem.Function(var2, pairtype)),
      "true" -> TypeSystem.Bool,
      "cond" -> TypeSystem.Function(TypeSystem.Bool, TypeSystem.Function(var3, TypeSystem.Function(var3, var3))),
      "zero" -> TypeSystem.Function(TypeSystem.Integer, TypeSystem.Bool),
      "pred" -> TypeSystem.Function(TypeSystem.Integer, TypeSystem.Integer),
      "times"-> TypeSystem.Function(TypeSystem.Integer, TypeSystem.Function(TypeSystem.Integer, TypeSystem.Integer))
    )


    val pair = Apply(Apply(Ident("pair"), Apply(Ident("f"), Ident("4"))), Apply(Ident("f"), Ident("true")))

    for(eg <- asts)
     yield tryTypeCheck(myenv, eg)

  }

  def tryexp(env: TypeSystem.Env, ast: SyntaxNode) {
    print(SyntaxNode.string(ast) + " : ")
    try {
      val t = TypeSystem.analyse(ast, env)
      print(TypeSystem.string(t))

    }catch{
      case t: ParseError => print(t.getMessage)
      case t: TypeError => print(t.getMessage)
    }
    println
  }

  def tryTypeCheck(env: TypeSystem.Env, ast: SyntaxNode): String = {
    val typeStr = try {
      val t = TypeSystem.analyse(ast, env)
      TypeSystem.string(t)

    }catch{
      case t: ParseError => t.getMessage
      case t: TypeError => t.getMessage
    }
    " : " + typeStr
  }

  def printlnEnv(env: TypeSystem.Env) {
    println("env:----------------")
    env.foreach { case (k, v) =>
      println(s"$k -> ${TypeSystem.string2(v)}")
    }
    println("--------------------")
  }
}

/*
(letrec factorial = (fn n ⇒ (((cond (zero n)) 1) ((times n) (factorial (pred n))))) in (factorial 5)) : int
(fn x ⇒ ((pair (x 3)) (x true))) : Type mismatch: bool≠int
((pair (f 4)) (f true)) : Undefined symbol f
(let f = (fn x ⇒ x) in ((pair (f 4)) (f true))) : (int × bool)
(fn f ⇒ (f f)) : recursive unification
(let g = (fn f ⇒ 5) in (g g)) : int
(fn g ⇒ (let f = (fn x ⇒ g) in ((pair (f 3)) (f true)))) : (α → (α × α))
(fn f ⇒ (fn g ⇒ (fn arg ⇒ (g (f arg))))) : ((β → γ) → ((γ → δ) → (β → δ)))
*/
