/**
 * a Scala package for arithmetic operations with
 * ordered rooted binary trees using "generalized constructors"
 */
package treenums

/**
 * case classes for our "real" constructors/destructors T/0,C/2
 */
trait AlgT {
  /**
   *  successor
   */
  def s(z: AlgT): AlgT = z match {
    case T       => C(T, T)
    case C(T, y) => d(s(y))
    case z       => C(T, h(z))
  }

  /**
   * double of non-zero
   */

  def d(z: AlgT): AlgT = z match {
    case C(x, y) => C(s(x), y)
  }

  /**
   * half of non-zero even
   */

  def h(z: AlgT): AlgT = z match {
    case C(x, y) => C(p(x), y)
  }

  /**
   *  predecessor
   */
  def p(z: AlgT): AlgT = z match {
    case C(T, T) => T
    case C(T, y) => d(y)
    case z       => C(T, p(h(z)))
  }

}

case object T extends AlgT
case class C(l: AlgT, r: AlgT) extends AlgT

/**
 * defintion of "generalized" constructor/destructor S
 * representing the successor function x<->x+1 on binary trees of type AlgT
 * their apply and unapply functions are expressed in terms of our
 * "real" constructors
 */
object S extends AlgT {
  def apply(x: AlgT) = s(x)

  def unapply(x: AlgT) = x match {
    case C(_, _) => Some(p(x))
    case T       => None
  }
}

/**
 * definition of generalized constructor/destructor D
 * representing double/half
 */
object D extends AlgT {
  def apply(x: AlgT) = d(x)

  def unapply(x: AlgT) = x match {
    case C(C(_, _), _) => Some(h(x))
    case _             => None
  }
}

/**
 * defintion of "generalized" constructor/destructor O
 * representing x<->2*x+1 on binary trees of type AlgT
 */
object O extends AlgT {
  def apply(x: AlgT) = C(T, x)

  def unapply(x: AlgT) = x match {
    case C(T, b) => Some(b)
    case _       => None
  }
}

/**
 * defintion of "generalized" constructor/destructor I
 * representing x<->2*x+2 on binary trees of type AlgT
 */
object I extends AlgT {
  def apply(x: AlgT) = S(O(x))

  def unapply(x: AlgT) = x match {
    case D(a) => Some(p(a))
    case _    => None
  }
}

trait Tcompute extends AlgT {

  val LT = -1
  val EQ = 0
  val GT = 1

  private def strengthen(rel: Int, from: Int) = rel match {
    case EQ => from
    case _  => rel
  }

  /**
   * comparaison function returning LT,EQ,GT
   */
  def cmp(u: AlgT, v: AlgT): Int = (u, v) match {
    case (T, T)       => EQ
    case (T, _)       => LT
    case (_, T)       => GT
    case (O(x), O(y)) => cmp(x, y)
    case (I(x), I(y)) => cmp(x, y)
    case (O(x), I(y)) => strengthen(cmp(x, y), LT)
    case (I(x), O(y)) => strengthen(cmp(x, y), GT)
  }

  /**
   * addition operation on binary trees, corresponding
   * to addition on N
   */
  def add(u: AlgT, v: AlgT): AlgT = (u, v) match {
    case (T, y)       => y
    case (x, T)       => x
    case (O(x), O(y)) => I(add(x, y))
    case (O(x), I(y)) => O(S(add(x, y)))
    case (I(x), O(y)) => O(S(add(x, y)))
    case (I(x), I(y)) => I(S(add(x, y)))
  }

  /**
   * subtraction operation on binary trees, corresponding
   * to subtraction on N
   */
  def sub(u: AlgT, v: AlgT): AlgT = (u, v) match {
    case (x, T)       => x
    case (O(x), O(y)) => p(O(sub(x, y)))
    case (O(x), I(y)) => p(p(O(sub(x, y))))
    case (I(x), O(y)) => O(sub(x, y))
    case (I(x), I(y)) => p(O(sub(x, y)))
  }

  /**
   * multiplication operation on binary trees, corresponding
   * to multiplication on N
   */
  def multiply(u: AlgT, v: AlgT): AlgT = (u, v) match {
    case (T, _) => T
    case (_, T) => T
    case (C(hx, tx), C(hy, ty)) => {
      val v = add(tx, ty)
      val z = p(O(multiply(tx, ty)))
      C(add(hx, hy), add(v, z))
    }
  }

  /**
   * exponent of 2 : a constant time operation
   */
  def exp2(x: AlgT) = C(x, T)

  /**
   * power operation on binary trees, corresponding
   * to u at exponent v on N
   */
  def pow(u: AlgT, v: AlgT): AlgT = (u, v) match {
    case (_, T)    => C(T, T)
    case (x, O(y)) => multiply(x, pow(multiply(x, x), y))
    case (x, I(y)) => {
      val xx = multiply(x, x)
      multiply(xx, pow(xx, y))
    }
  }

  /**
   * division with remainder operation on binary trees, corresponding
   * to the same on N
   */
  def div_and_rem(x: AlgT, y: AlgT): (AlgT, AlgT) =
    if (cmp(x, y) == LT) (T, x)
    else if (T == y) null // division by zero
    else {
        //println("div>>" + toN(x) + "/" + toN(y))
        def try_to_double(x: AlgT, y: AlgT, k: AlgT): AlgT =
          if (cmp(x, y) == LT) p(k)
          else try_to_double(x, d(y), S(k))

        def divstep(n: AlgT, m: AlgT): (AlgT, AlgT) = {
          val q = try_to_double(n, m, T)
          val p = multiply(exp2(q), m)
          (q, sub(n, p))
        }
      val (qt, rm) = divstep(x, y)
      val (z, r) = div_and_rem(rm, y)
      val dv = add(exp2(qt), z)
      (dv, r)
    }

  /**
   * division
   */
  def divide(x: AlgT, y: AlgT) = div_and_rem(x, y)._1

  /**
   * reminder
   */
  def reminder(x: AlgT, y: AlgT) = div_and_rem(x, y)._2

  /**
   * greatest common divisor
   */
  def gcd(x: AlgT, y: AlgT): AlgT = if (y == T) x else gcd(y, reminder(x, y))

  /**
   * least common multiplier
   */
  def lcm(x: AlgT, y: AlgT): AlgT = multiply(divide(x, gcd(x, y)), y)
}

trait Tconvert {
  /**
   * converter from natural numbers represented as BigInt objects
   */
  def fromN(i: BigInt): AlgT = {
      def oddN(i: BigInt) =
        i.testBit(0)

      def evenN(i: BigInt) =
        i != BigInt(0) && !i.testBit(0)

      def hN(x: BigInt): BigInt =
        if (oddN(x))
          BigInt(0)
        else
          BigInt(1) + hN(x >> 1)

      def tN(x: BigInt): BigInt =
        if (oddN(x))
          (x - BigInt(1)) >> 1
        else
          tN(x >> 1)

    if (0 == i) T
    else C(fromN(hN(i)), fromN(tN(i)))
  }

  /**
   * converter to natural numbers represented as BigInt objects
   */
  def toN(z: AlgT): BigInt = z match {
    case T => 0
    case C(x, y) =>
      (BigInt(1) << toN(x).intValue()) *
        (BigInt(2) * toN(y) + 1)
  }
}

trait Q extends Qcode {
  def toFraq(): (BigInt, BigInt) = this match {
    case Z         => (0, 1)
    case M((a, b)) => (-(toN(a)), toN(b))
    case P((a, b)) => (toN(a), toN(b))
  }
}

case object Z extends Q
case class P(x: (AlgT, AlgT)) extends Q
case class M(x: (AlgT, AlgT)) extends Q

trait Qcode extends Tcompute with Tconvert {
  type PQ = (AlgT, AlgT)
  /**
   * Rationals - first step:
   *
   * Variant of Dijkstra's fusc function from the Calkin-Wilf paper
   * providing a constructive bijection between Naturals and positive
   * rationals
   */
  def cw(u: AlgT): AlgT = u match {
    case T    => S(T)
    case O(x) => cw(x)
    case I(x) => add(cw(x), cw(S(x)))
  }

  /**
   * splits u seen as a natural number into its
   * corresponding Calkin-Wilf rational, represented
   * as a pair
   */
  def t2pq(u: AlgT): PQ = u match {
    case T => (S(T), S(T))
    case O(n) => {
      val (x, y) = t2pq(n)
      (x, add(x, y))
    }
    case I(n) => {
      val (x, y) = t2pq(n)
      (add(x, y), y)
    }
  }

  /**
   * fuses back into a "natural number",
   * representing the path in the Calkin-Wilf tree,
   * a pair of co-prime natural numbers representing
   * the (numerator,denominator) of a positive rational number
   */
  def pq2t(uv: PQ): AlgT = uv match {
    case (O(T), O(T)) => T
    case (a, b) =>
      cmp(a, b) match {
        case GT => I(pq2t(sub(a, b), b))
        case LT => O(pq2t(a, sub(b, a)))
      }
  }

  /**
   * Signed Rationals from trees seen as natural numbers
   */
  def fromT(t: AlgT): Q = t match {
    case T    => Z // zero -> zero
    case O(x) => M(t2pq(x)) // odd -> negative
    case I(x) => P(t2pq(x)) // even -> positive
  }

  /**
   * From Signed Rationals to trees seen as natural numbers
   */
  def toT(q: Q): AlgT = q match {
    case Z    => T // zero -> zero
    case M(x) => O(pq2t(x)) // negative -> odd
    case P(x) => I(pq2t(x)) // positive -> even
  }

  /**
   * bijection from BigInt natural numbers to
   * tree-represented Signed Rationals
   */
  def nat2rat(n: BigInt): Q = fromT(fromN(n))

  /**
   * bijection from tree-represented Signed Rationals to
   * BigInt natural numbers
   */
  def rat2nat(q: Q): BigInt = toN(toT(q))

  def fraq2pq(nd: (BigInt, BigInt)): PQ =
    pqsimpl((fromN(nd._1), fromN(nd._2)))

  def pq2fraq(nd: PQ): (BigInt, BigInt) =
    (toN(nd._1), toN(nd._2))

  /**
   * simplifies a positive fraction represented as a pair
   */
  def pqsimpl(xy: PQ) = {
    val x = xy._1
    val y = xy._2
    val z = gcd(x, y)
    (divide(x, z), divide(y, z))
  }

  /**
   * addition/subtraction template
   */
  def pqop(f: (AlgT, AlgT) => AlgT, xy: PQ, uv: PQ): PQ = {
    val (x, y) = xy
    val (u, v) = uv
    val z = gcd(y, v)
    val y1 = divide(y, z)
    val v1 = divide(v, z)
    val num = f(multiply(x, v1), multiply(u, y1))
    val den = multiply(z, multiply(y1, v1))
    pqsimpl((num, den))
  }

  def pqadd(a: PQ, b: PQ) = pqop(add, a, b)
  def pqsub(a: PQ, b: PQ) = pqop(sub, a, b)

  def pqcmp(xy: PQ, uv: PQ) = {
    val (x, y) = xy
    val (u, v) = uv
    cmp(multiply(x, v), multiply(y, u))
  }
  def pqmultiply(a: PQ, b: PQ) =
    pqsimpl(multiply(a._1, b._1), multiply(a._2, b._2))

  def pqinverse(a: PQ) = (a._2, a._1)

  def pqdivide(a: PQ, b: PQ) = pqmultiply(a, pqinverse(b))

  // operations on signed rationals

  def ropposite(x: Q) = x match {
    case Z    => Z
    case M(a) => P(a)
    case P(a) => M(a)

  }

  def radd(a: Q, b: Q): Q = (a, b) match {
    case (Z, y)       => y
    case (M(x), M(y)) => M(pqadd(x, y))
    case (P(x), P(y)) => P(pqadd(x, y))
    case (P(x), M(y)) => pqcmp(x, y) match {
      case LT => M(pqsub(y, x))
      case EQ => Z
      case GT => P(pqsub(x, y))
    }
    case (M(x), P(y)) => ropposite(radd(P(x), M(y)))
  }

  def rsub(a: Q, b: Q) = radd(a, ropposite(b))

  def rmultiply(a: Q, b: Q): Q = (a, b) match {
    case (Z, _)       => Z
    case (_, Z)       => Z
    case (M(x), M(y)) => P(pqmultiply(x, y))
    case (M(x), P(y)) => M(pqmultiply(x, y))
    case (P(x), M(y)) => M(pqmultiply(x, y))
    case (P(x), P(y)) => P(pqmultiply(x, y))
  }

  def rinverse(a: Q) = a match {
    case M(x) => M(pqinverse(x))
    case P(x) => P(pqinverse(x))
  }

  def rdivide(a: Q, b: Q) =
    rmultiply(a, rinverse(b))

}

