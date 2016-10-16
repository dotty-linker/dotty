package test

import scala.annotation.Idempotent

object CommonSubexpression {

  @Idempotent def sum(i1: Int, i2: Int) = i1 + i2
  @Idempotent def sum2[A: Numeric, B: Numeric](i1: A, i2: B) =
    implicitly[Numeric[A]].toInt(i1) + implicitly[Numeric[B]].toInt(i2)
  @Idempotent def div(i1: Int, i2: Int) = i1 / i2

  def method1: Int = {
    val a = 1
    val c = sum(sum(1, a), 3)
    val d = sum(sum(1, a), 4)
    assert(c == 5)
    assert(d == 6)
    d - c
  }

  def method2: Int = {
    val a = 1
    val c = sum(sum(sum(1, a), 2), 3)
    val d = sum(sum(sum(1, a), 2), 4)
    assert(c == 7)
    assert(d == 8)
    d - c
  }

  def method3: Int = {
    val a = 1
    val c = sum(sum(sum(1, a), 2), 1)
    val d = sum(sum(sum(1, a), 2), 2)
    assert(c == 5)
    assert(d == 6)
    d - c
  }

  def method4: Int = {
    val a = 1
    val b = sum(1, a)
    val c = sum(sum(sum(1, a), 2), 1)
    val d = sum(sum(sum(1, a), 2), 2)
    assert(b == 2)
    assert(c == 5)
    assert(d == 6)
    d - c
  }

  def method5: Int = {
    val a = 1
    val b = sum(1, a)
    val c = sum(sum(1, a), 2)
    val d = sum(sum(sum(1, a), 2), 2)
    assert(b == 2)
    assert(c == 4)
    assert(d == 6)
    d - c
  }

  def method6: Int = {
    val a = 1
    val c = 3 + sum(1, a)
    val d = sum(1, a) + 4
    assert(c == 5)
    assert(d == 6)
    d - c
  }

  def method7: Int = {
    val a = (1,1)
    val c = 3 + a._1
    val d = a._1 + 3
    assert(c == 4)
    assert(d == 4)
    d - c
  }

  def method8: Int = {
    val a = 1
    val c = 3 + sum2(a, a)
    val d = sum2(a, a) + 3
    assert(c == 5)
    assert(d == 5)
    d - c
  }

  // Method equals are optimized
  case class Foo(a: Int)
  case class Bar(f: Foo)

  def method9: Boolean = {
    val a1 = Bar(Foo(1))
    val a2 = Bar(Foo(1))
    a1.equals(a2)
  }

  def method10: Boolean = {
    class A
    class B extends A
    class C extends A
    val a: A = new B
    val b = a.isInstanceOf[B]
    val c = a.isInstanceOf[B]
    b && c
  }

  def method11: Int = {
    val a = Bar(Foo(1))
    val c = 3 + sum2(a.f.a, a.f.a)
    val d = sum2(a.f.a, a.f.a) + 3
    assert(c == 5)
    assert(d == 5)
    d - c
  }

  def method12b: Int = {
    val a = Bar(Foo(1))
    val c = 3 + sum2(a.f.a, a.f.a)
    val d = sum2(a.f.a, a.f.a) + 3
    val e = 3 + sum2(sum2(a.f.a, a.f.a), sum2(a.f.a, a.f.a))
    val f = sum2(sum2(a.f.a, a.f.a), sum2(a.f.a, a.f.a)) + 3
    assert(c == 5)
    assert(d == 5)
    assert(e == 13)
    assert(f == 13)
    d - c
  }

  def method12: Int = {
    class A(val a: Int) {
      @Idempotent def sum[N: Numeric](b: N) =
        a + implicitly[Numeric[N]].toInt(b)
    }

    val a = new A(1)
    val b = a.sum(2)
    val c = a.sum(2) + 1
    assert(b == 3)
    assert(c == 4)
    c - b
  }

  def method13: Int = {
    class A(val a: Int) {
      @Idempotent def convert[N: Numeric]: N =
        implicitly[Numeric[N]].fromInt(a)
    }

    val a = new A(1)
    val b = a.convert[Int]
    val c = a.convert[Int]
    assert(b == 1)
    assert(c == 1)
    c - b
  }

  def method14: Int = {
    val a = 1
    val c = () => {
      val b = sum(sum(1, a), 3)
      b + 1 - 1
    }
    val c2 = c()
    val d = sum(sum(1, a), 4)
    assert(c2 == 5)
    assert(d == 6)
    d - c2
  }

  def method15: Int = {
    val a = 1
    val c = {
      val e = () => {
        val b = sum(sum(1, a), 3)
        b + 1 - 1
      }
      e()
    }
    val d = sum(sum(1, a), 4)
    assert(c == 5)
    assert(d == 6)
    d - c
  }

  def method17: Unit = {
    val a = 1
    val b = div(a, 0)
    assert(b == 0)
    val c = try {
      val e = div(a, 0)
    } catch { case e: Exception => 0 }
    assert(c == 0)
  }

  def method17b: Unit = {
    val a = 1
    val b = try {
      val d = div(a, 0)
    } catch { case e: Exception => 0}
    assert(b == 0)
    val c = try {
      val e = div(a, 0)
    } catch { case e: Exception => 0 }
    assert(c == 0)
  }

  def method18: Unit = {
    val a = 1
    val b = try {
      div(a, 0)
    } catch { case e: Exception => 0}
    assert(b == 0)
    val c = try {
      div(a, 0)
    } catch { case e: Exception => 0 }
    assert(c == 0)
  }

  def method18b: Unit = {
    val a = 1
    val b = try {
      div(a, 0)
    } catch { case e: Exception => 0}
    finally ()
    assert(b == 0)
    val c = try {
      div(a, 0)
    } catch { case e: Exception => 0 }
    assert(c == 0)
  }

  def method19: Int = {
    val a = 1
    if (a == 1) {
      val b = sum(a, a)
      val c = sum(a, a) + 1
      b + c
    } else {
      val b = sum(a, a)
      b + 1
    }

  }

  def method20: Int = sum(sum(1, 1), sum(1, 1))

  def method21: Int = {
    val a = 1
    if (a == 1) {
      if (a == 2) {
        val b = sum(a, a)
      }
      val c = sum(a, a) + 1
      c + c - 1
    } else {
      val b = sum(a, a)
      b + 1
    }

  }

  def method22: Int = {
    val a = 1
    if (a == 1) {
      if (a == 1) sum(a, a)
      else sum(a, a)
    } else sum(a, a)
    println("DABEI")
    sum(a, a)
  }

  // DON'T OPTIMIZE IT
  def method22b: Int = {
    val a = 1
    if (a == 1) {
      if (a == 1) sum(a, a)
    } else sum(a, a)
    println("DABEI")
    sum(a, a)
  }

  def method23 = {
    val a = 1
    if (a == 1 || a == 2) {
      if (a == 1) sum(a, a)
      else sum(a, a)
    } else sum(a, a)
    sum(a, a)
  }

  def method24 = {
    val a = 1
    if (a == 1 && a == 2) {
      if (a == 2) sum(a, a)
      else sum(a, a)
    } else sum(a, a)
    sum(a, a)
  }

  def method24b = {
    val a = 1
    if (a == 1 && a == 1 && a == 2) {
      if (a == 2 && a == 1) sum(a, a)
      else sum(a, a)
    } else sum(a, a)
    sum(a, a)
  }

  def method25 = {
    val a = 1
    if (a == 1 ^ a == 2) {
      if (a == 1 ^ a == 2) sum(a, a)
      else sum(a, a)
    } else sum(a, a)
    sum(a, a)
  }

  def method25b = {
    val a = 1
    if (a == 2 ^ a == 1 ^ a == 2) {
      if (a == 1 ^ a == 2) sum(a, a)
      else sum(a, a)
    } else sum(a, a)
    sum(a, a)
  }

  def method26NotOptimize = {
    val d: Double = null.asInstanceOf[Double]
    println(d)
    val f: Foo = null.asInstanceOf[Foo]
    println(f)
  }

  def method27= {
    scala.math.Numeric.BigDecimalAsIfIntegral
    scala.math.Numeric.ByteIsIntegral
  }

  def mixinsNotOptimize = {
    class M1 {
      def f = "M1::f"
    }

    trait M2 {
      def f = "M2::f"
    }

    trait M3 {
      def f = "M3::f"
    }

    class Host extends M1 with M2 with M3 {
      override def f = super[M1].f + " " + super[M2].f + " " + super[M3].f
    }

    (new Host).f
  }

  def main(args: Array[String]): Unit = {
    println("executing")
    assert(method1 == 1)
    assert(method2 == 1)
    assert(method3 == 1)
    assert(method4 == 1)
    assert(method5 == 2)
    assert(method6 == 1)
    assert(method7 == 0)
    assert(method8 == 0)
    assert(method9)
    assert(method10)
    assert(method11 == 0)
    assert(method12 == 1)
    assert(method13 == 0)
    assert(method14 == 1)
    assert(method15 == 1)
    // method17
    //method18
    assert(method19 == 5)
    assert(mixinsNotOptimize == "M1::f M2::f M3::f")
  }

}
