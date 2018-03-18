package jsy.student

import jsy.lab4.Lab4Like

object Lab4 extends jsy.util.JsyApplication with Lab4Like {
  import jsy.lab4.ast._
  import jsy.lab4.Parser

  /*
   * CSCI 3155: Lab 4
   * <Matt Moore>
   *
   * Partner: <Jonathan Young>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   *
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */

  /* Collections and Higher-Order Functions */

  /* Lists */

  def compressRec[A](l: List[A]): List[A] = l match {
    case Nil | _ :: Nil => l
    case h1 :: (t1 @ (h2 :: _)) => if (h1 == h2) compressRec(t1) else h1 :: compressRec(t1)
  }

  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) => acc match {
      case Nil => h :: Nil
      case h1 :: _ => if (h1 == h) acc else h :: acc
    }
  }

  def mapFirst[A](l: List[A])(f: A => Option[A]): List[A] = l match {
    case Nil => l
    case h :: t => f(h) match {
      case None => h :: mapFirst(t){f}
      case Some(x) => x :: t
    }
  }

  /* Trees */

  def foldLeft[A](t: Tree)(z: A)(f: (A, Int) => A): A = {
    def loop(acc: A, t: Tree): A = t match {
      case Empty => acc
      case Node(l, d, r) => {
        loop(f(loop(acc, l), d), r)
      }
    }
    loop(z, t)
  }

  // An example use of foldLeft
  def sum(t: Tree): Int = foldLeft(t)(0){ (acc, d) => acc + d }

  // Create a tree from a list. An example use of the
  // List.foldLeft method.
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }

  def strictlyOrdered(t: Tree): Boolean = {
    val (b, _) = foldLeft(t)((true, None: Option[Int])){
      (acc, h) => acc match {
        case (false, _) => (false, None)
        case (true, None) => (true, Some(h))
        case (true, Some(i)) => (h > i, Some(h))
        case (b, _) => (b, Some(h))
      }
    }
    b
  }

  /* Type Inference */

  // While this helper function is completely given, this function is
  // worth studying to see how library methods are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }

  def typeof(env: TEnv, e: Expr): Typ = {
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typeof(env, e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) => env(x)
      case Decl(mode, x, e1, e2) => typeof(extend(env, x, typeof(env, e1)), e2)
      case Unary(Neg, e1) => typeof(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) => typeof(env, e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      case Binary(Plus, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TString, TString) => TString
        case (TNumber, TNumber) => TNumber
        case (a, tgot) => if (a != tgot) err(tgot, e2) else tgot
        case (tgot, _) => err(tgot, e1)
      }
      case Binary(Minus|Times|Div, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TNumber, tgot) => err(tgot, e2)
        case (tgot, _) => err(tgot, e1)
      }
      case Binary(Eq|Ne, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (t1, t2) if t1 == t2 => TBool
        case (tgot, _) if hasFunctionTyp(tgot) => err(tgot, e1)
        case (_ , tgot) if hasFunctionTyp(tgot)=> err(tgot, e2)
        case (t1, t2) if t1 != t2 => err(t2, e2)
        case _ => TBool
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TBool
        case (TString, TString) => TString
        case (TString | TNumber, tgot) => err(tgot, e2)
        case (tgot, _) => err(tgot, e1)
      }
      case Binary(And|Or, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case(TBool, TBool) => TBool
        case (TBool, tgot) => err(tgot, e2)
        case (tgot, _) => err(tgot, e1)
      }
      case Binary(Seq, e1, e2) => typeof(env, e2)
      case If(e1, e2, e3) => (typeof(env, e1), typeof(env, e2), typeof(env, e3)) match {
        case (TBool, t2, t3) => if (t2 == t3) t2 else err(t3, e3)
        case (tgot, _, _) => err(tgot, e1)
      }
      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          /***** Add cases here *****/
          case (Some(p1), Some(t)) => {
            extend(env, p1, TFunction(params, t))
          }
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = {
          params.foldLeft(env1) {
            case (acc, (s, MTyp(_, t))) => acc + (s -> t)
          }
        }
        // Infer the type of the function body
        val t1 = typeof(env2, e1)
        // Check with the possibly annotated return type
        tann match {
          case None => TFunction(params, t1)
          case Some(t) => if (t1 == t) TFunction(params, t1) else err(TFunction(params, t1), e1)
        }
      }
      case Call(e1, args) => typeof(env, e1) match {
        case TFunction(params, tret) if (params.length == args.length) =>
          (params zip args).foreach {
            case ((string, mtyp), a) => if (mtyp.t != typeof(env, a)) err(typeof(env, a), a)
          };
          tret
        case tgot => err(tgot, e1)
      }
      case Obj(fields) => TObj(fields.map{ case (s,e) => (s,typeof(env, e))})
      case GetField(e1, f) => /*e1 match {
        case Obj(fields) => if (fields.contains(f)) typeof(env, fields.get(f).get) else err(typeof(env, e1) ,e1)
        case _ => err(typeof(env, e1), e1)
      }*/
        typeof(env, e1) match {
          case TObj(tfields) => tfields(f)
          case x => err(x, e1)
        }
    }
  }


  /* Small-Step Interpreter */

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), s"inequalityVal: v1 ${v1} is not a value")
    require(isValue(v2), s"inequalityVal: v2 ${v2} is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) => bop match {
        case Lt => s1 < s2
        case Le => s1 <= s2
        case Gt => s1 > s2
        case Ge => s1 >= s2
      }
      case (N(n1), N(n2)) => bop match {
        case Lt => n1 < n2
        case Le => n1 <= n2
        case Gt => n1 > n2
        case Ge => n1 >= n2
      }
    }
  }

  /* This should be the same code as from Lab 3 */
  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e, n) match {
      case Some(e) => loop(e, n+1)
      case None => e
    }
    loop(e0, 0)
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, esub, x))
        /***** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if (x == y) esub else Var(y)
      case Decl(mode, y, e1, e2) => {
        if (x == y)
          Decl(mode, y, subst(e1), e2)
        else
          Decl(mode, y, subst(e1), subst(e2))
      }
        /***** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1) => {
        if (params.forall{ case (s : String, mtyp : MTyp) => x != s })
          Function(p, params, tann, e1)
        else
          Function(p, params, tann, subst(e1))
      }
      case Call(e1, args) => Call(subst(e1), args.map{ arg => subst(arg) })
        /***** New cases for Lab 4 */
      case Obj(fields) => Obj(fields.map{ case (f, e) => (f, subst(e))})
      case GetField(e1, f) => GetField(subst(e1), f)
    }

    val fvs = freeVars(e)
    def fresh(x: String): String = if (fvs.contains(x)) fresh(x + "$") else x
    subst(rename(e)(fresh))
  }

  /* Rename bound variables in e */
  def rename(e: Expr)(fresh: String => String): Expr = {
    def ren(env: Map[String,String], e: Expr): Expr = {
      e match {
        case N(_) | B(_) | Undefined | S(_) => e
        case Print(e1) => Print(ren(env, e1))

        case Unary(uop, e1) => Unary(uop, ren(env, e1))
        case Binary(bop, e1, e2) => Binary(bop, ren(env, e1), ren(env, e2))
        case If(e1, e2, e3) => If(ren(env, e1), ren(env, e2), ren(env, e3))

        case Var(y) => env.get(y) match {
          case Some(x) => Var(x)
          case None => Var(y)
        }
        case Decl(mode, y, e1, e2) =>
          val yp = fresh(y)
          //y is bound, don't change
          if (y == yp)
            Decl(mode, y, ren(env, e1), ren(env, e2))
          else {
            Decl(mode, yp, ren(env, e1), ren(env + (y -> yp), e2))
          }

        case Function(p, params, retty, e1) => {
          val (pp, envp): (Option[String], Map[String,String]) = p match {
            case None => (p, env)
            case Some(x) => {
              val xp = fresh(x)
              if (x == xp)
                (Some(x), env)
              else
                (Some(xp), env + (x ->xp))
            }
          }
          val (paramsp, envpp) = params.foldRight( (Nil: List[(String,MTyp)], envp) ) {
            case ((x,mtyp), (newParams, envp)) => {
              val xp = fresh(x)
              if (x == xp)
                (newParams :+ (xp, mtyp), envp)
              else
                (newParams :+ (xp, mtyp), envp + (x -> xp))
            }
          }
          Function(pp, paramsp, retty, ren(envpp, e1))
        }

        case Call(e1, args) => Call(ren(env, e1), args.map{ arg => ren(env, arg) })

        case Obj(fields) => Obj(fields.map{ case (f, e) => (f, ren(env, e))})
        case GetField(e1, f) => GetField(ren(env, e1), f)
      }
    }
    ren(empty, e)
  }

  /* Check whether or not an expression is reduced enough to be applied given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = mode match {
    case MConst => !isValue(e)
    case MName => false
  }

  def step(e: Expr): Expr = {
    require(!isValue(e), s"step: e ${e} to step is a value")
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
        /***** Cases needing adapting from Lab 3. */
      case Unary(Neg, N(n1)) => N(-n1)
      case Unary(Not, B(b1)) => B(!b1)
      case Binary(Seq, v1, e2) if isValue(v1) => e2
      case Binary(arith @ (Plus|Minus|Times|Div), N(n1), N(n2)) => arith match {
        case Plus => N(n1 + n2)
        case Minus => N(n1 - n2)
        case Times => N(n1 * n2)
        case Div => N(n1 / n2)
      }
      case Binary(Plus, S(s1), S(s2)) => S(s1+s2)

      case Binary(ineq @ (Lt|Le|Gt|Ge), N(n1), N(n2)) => B(inequalityVal(ineq, N(n1), N(n2)))
      case Binary(ineq @ (Lt|Le|Gt|Ge), S(s1), S(s2)) => B(inequalityVal(ineq,  S(s1),S(s2)))
      case Binary(eq @ (Eq|Ne), v1, v2) if isValue(v1) && isValue(v2) => eq match {
        case Eq => B(v1 == v2)
        case Ne => B(v1 != v2)
      }

      case Binary(And, B(b1), e2) => if (b1) e2 else B(b1)
      case Binary(Or, B(b1), e2) => if (b1) B(b1) else e2

      case If(v1, v2, v3) if isValue(v1) => v1 match {
        case B(b1) => if (b1) v2 else v3
      }

      case Decl(mode, x, e1, e2) if !isRedex(mode, e1) => substitute(e2, e1, x)
        /***** More cases here */
      case Call(v1, args) if isValue(v1) =>
        v1 match {
          case Function(p, params, _, e1) => {
            val pazip = params zip args
            if (pazip.forall{ case ((s, MTyp(m, t)), e) => !isRedex(m, e) }) {
              val e1p = pazip.foldRight(e1) {
                case (((s,_), e), ebody) => substitute(ebody, e, s)
              }
              p match {
                case None => e1p
                case Some(x1) => substitute(e1p, e1, x1)
              }
            }
            else {
              //SearchCall for args
              val newZip = mapFirst(pazip) {
                case ((s, MTyp(m, t)), e) => if(isRedex(m, e)) Some(((s, MTyp(m, t)), step(e))) else None
              }

              val newArgs = newZip.map{ case ((s, MTyp(m, t)), e) => e}
              Call(v1, newArgs)
            }
          }
          case _ => throw StuckError(e)
        }
        /***** New cases for Lab 4. */

      case GetField(e1, f) if isValue(e1) => e1 match
      {
        case Obj(map) => map.get(f) match {
          case Some(e) => e
          case None => throw StuckError(e)
        }
        case _ => throw StuckError(e)
      }
      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
        /***** Cases from Lab 3. */
      case Unary(uop, e1) => Unary(uop, step(e1))
      case Binary(bop, v1, e2) if isValue(v1) => Binary(bop, v1, step(e2))
      case Binary(bop, e1, e2) => Binary(bop, step(e1), e2)
      case If(e1, e2, e3) => If(step(e1), e2, e3)
        /***** More cases here */
        /***** Cases needing adapting from Lab 3 */
      case Call(e1, args) => Call(step(e1), args)
      case Decl(m, x, e1, e2) => Decl(m, x, step(e1), e2)
        /***** New cases for Lab 4. */
      case GetField(e1, f) => GetField(step(e1), f)
      case Obj(map) => map find (f => !isValue(f._2)) match
      {
        case Some((s, exp)) => Obj(map + (s -> step(exp)))
        case _ => throw StuckError(e)
      }

      /* Everything else is a stuck error. Should not happen if e is well-typed.
       *
       * Tip: you might want to first develop by comment out the following line to see which
       * cases you have missing. You then uncomment this line when you are sure all the cases
       * that you have left the ones that should be stuck.
       */
      case _ => throw StuckError(e)
    }
  }


  /* External Interfaces */

  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
}

