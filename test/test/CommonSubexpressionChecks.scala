package test

import scala.annotation.Idempotent

class A {
  var count = 0

  @Idempotent def idem1: Int = {
    count += 1
    count
  }

  @Idempotent def idem2(): Int = {
    count += 1
    count
  }

  @Idempotent def idem3(a: Int): Int = {
    count += 1
    count
  }

  @Idempotent def idem4(a: Int, b: Int): Int = {
    count += 1
    count
  }

  @Idempotent def idem5[T1, T2](a: T1)(b: T2): Int = {
    count += 1
    count
  }

  def test1(): Unit = {
    val a = idem1
    val b = idem1

    assert(count == 1)
    count = 0
  }

  def test2(): Unit = {
    val a = idem2()
    val b = idem2()

    assert(count == 1)
    count = 0
  }

  def test3(): Unit = {
    val a = idem2
    val b = idem2()

    assert(count == 1)
    count = 0
  }

  def test4(): Unit = {
    val a = idem2()
    val b = idem2

    assert(count == 1)
    count = 0
  }

  def test5(): Unit = {
    val a = idem1 + idem2()
    val b = idem1 + idem2()

    assert(count == 2)
    count = 0
  }

  def test6(): Unit = {
    val a = idem1
    (1 to 10) map (_ => idem1)

    assert(count == 1)
    count = 0
  }

  def test6bis(): Unit = {
    (1 to 10) map (_ => idem1)

    assert(count == 10)
    count = 0
  }

  def test7(): Unit = {
    val a = idem3(idem1)
    val b = idem1
    val c = idem3(idem1)

    assert(count == 2)
    count = 0
  }

  def test8(a: A): Unit = {
    val i = a.idem1
    val i2 = idem1
    val i3 = this.idem1

    assert(a.count == 1)
    assert(count == 1)
    a.count = 0
    count = 0
  }

  def test9(): Unit = {
    val a = idem4(idem1, idem2())
    val b = idem4(idem1, idem2())

    assert(count == 3)
    count = 0
  }

  def test10(): Unit = {
    val a = idem4(idem1 + 1, idem2())
    val b = idem2()
    val c = idem1

    assert(count == 3)
    count = 0
  }

  def test11(): Unit = {
    var a = idem1
    val b = idem4(a, idem1)
    a = 3
    val c = idem4(a, idem1)

    assert(count == 3)
    count = 0
  }

  def test11bis(): Unit = {
    val v1 = new A
    val v2 = new A

    var a = v1
    val b = a.idem1
    a = v2
    val c = a.idem1

    assert(v1.count == 1)
    assert(v2.count == 1)
  }

  def test12(): Unit = {
    def impure = 1

    val a = idem4(impure, idem1)
    val b = idem1

    assert(count == 3)
    count = 0
  }

  def test13(): Unit = {
    def impure = new A

    val a = impure.idem3(idem1)
    val c = idem3(idem1)

    assert(count == 3)
    count = 0
  }

  def test14(): Unit = {
    def impure = 3

    val a = impure + idem1
    val b = impure + idem1

    assert(count == 2)
    count = 0
  }

  def test15(): Unit = {
    def impure = 3

    val a = idem1 + impure
    val b = impure + idem1

    assert(count == 1)
    count = 0
  }

  def test16(): Unit = {
    def impure = 5
    val a = idem4(3 + impure, idem1)
    val b = idem1

    assert(count == 3)
    count = 0
  }

  def test17(): Unit = {
    def impure = 5
    val a = idem4(idem1, impure)
    val b = idem1

    assert(count == 2)
    count = 0
  }

  def test18(): Unit = {
    def impure = 5
    val a = idem4(idem1 + impure, idem2())
    val b = idem1
    val c = idem2()

    assert(count == 4)
    count = 0
  }

  def test19(): Unit = {
    val a = idem3(1)
    val b = idem3(1)
    val c = idem4(2, 3)
    val d = idem4(2, 3)

    assert(count == 2)
    count = 0
  }

  def test20(): Unit = {
    val a = idem3(1)
    val b = idem3(2)
    val c = idem4(1, 3)
    val d = idem4(2, 3)

    assert(count == 4)
    count = 0
  }

  def test21(): Unit = {
    val a: Any = idem1
    val b = idem1

    assert(count == 1)
    count = 0
  }

  def test22(): Unit = {
    @Idempotent def foo(i: A, j: Int) = {
      count += 1
      j
    }

    val a = foo(this, 1)
    val b = foo(this, 1)
    assert(count == 1)
    count = 0
  }

  def test23(cond: Boolean): Unit = {
    val a = idem1

    if (cond) idem1 else idem1

    assert(count == 1)
    count = 0
  }

  def test24(cond: Boolean): Unit = {
    if (cond) idem1 else idem1
    val a = idem1

    assert(count == 2)
    count = 0
  }

  def test25(any: Any): Unit = {
    val a = idem1

    any match {
      case _: String => idem1
      case _ => idem1
    }

    assert(count == 1)
    count = 0
  }

  def test26(): Unit = {
    @Idempotent def idem = {
      count += 1
      true
    }

    if (idem) 1 else 2
    val a = idem

    assert(count == 1)
    count = 0
  }

  def test27(): Unit = {
    bar
    idem1
    def bar = {
      println("")
      idem1
    }

    assert(count == 2)
    count = 0
  }

  var c: Boolean = false
  def test27b(): Unit = {
    if (c) bar else bar
    idem1
    def bar = {
      println("")
      idem1
    }

    assert(count == 2)
    count = 0
  }

  def test27cNotOptimized(): Unit = {
    if (c) bar else ()
    idem1
    def bar = {
      println("")
      idem1
    }

    assert(count == 1)
    count = 0
  }

  def test27d(): Unit = {
    try {
      bar
    } catch {
      case t: Throwable =>
    }
    idem1
    def bar = idem1

    assert(count == 2)
    count = 0
  }

  def test27e(): Unit = {
    bar
    idem1
    def bar = {
      def bar2 = {
        println("A")
        idem1
        println("B")
      }
      bar2
    }

    assert(count == 2)
    count = 0
  }

  def test27f(): Unit = {
    bar1(1)
    idem1
    def bar1(a: Int) = {
      println("A")
      idem1
    }

    assert(count == 3)
    count = 0
  }

  def test27g(): Unit = {
    def foo(i: Any) = ()
    foo(if (bar1(1) == 1) 1 else 2)
    bar1(1)
    idem1
    def bar1(a: Int) = {
      println("A")
      idem1
    }

    assert(count == 3)
    count = 0
  }

  def test27hNonOptimizable(): Unit = {
    def foo(i: Any) = ()
    foo(if (c) bar1(1) else ())
    bar1(1)
    idem1
    def bar1(a: Int) = {
      println("A")
      idem1
    }

    assert(count == 3)
    count = 0
  }

  def test28(): Unit = {
    val a = idem1
    def bar = idem1
    bar

    assert(count == 1)
    count = 0
  }

  def test29(): Unit = {
    def bar = idem1
    val a = idem1
    bar

    assert(count == 1)
    count = 0
  }

  def test30(): Unit = {
    val a = idem5(1)("Hello")
    val b = idem5(1)("Hello")

    assert(count == 1)
    count = 0
  }

  def test31(): Unit = {
    val a = idem5(1)("Hello")
    val b = idem5[Int, String](1)("Hello")

    assert(count == 1)
    count = 0
  }

  def test32(): Unit = {
    def impure = 2
    val a = idem5(impure)(idem1)
    val b = idem1

    assert(count == 3)
    count = 0
  }

  def test33(): Unit = {
    def impure = 2
    val a = idem5(idem1)(impure)
    val b = idem1

    assert(count == 2)
    count = 0
  }

  def test34NotOptimizable(): Unit = {
    def foo(s: => Int) = s

    val a = foo(idem1)
    val b = idem1

    assert(count == 2)
    count = 0
  }

  def test35(): Unit = {
    def foo(i: Int) = idem1 + i
    foo(idem1)

    assert(count == 1)
    count = 0
  }

  def test36(): Unit = {
    def foo = idem1

    {
      idem1 // not reachable from foo body
      foo
    }

    assert(count == 2)
    count = 0
  }

  def test37(): Unit = {
    def foo = idem1 + idem2()
    val a = idem2()

    {
      idem1
      foo
    }

    {
      idem1
      foo
    }

    assert(count == 5)
    count = 0
  }

  def test38(): Unit = {
    @Idempotent def foo = idem1
    foo
    idem1
  }

  def test38b(): Unit = {
    val c = 1
    @Idempotent def foo: Int = idem1
    @Idempotent def sum(a: Int, b: Int) = { a + b + c + c }
    sum(c + c, foo + foo)
    foo + foo
  }

  def reg1(): Unit = {
    // TODO remove from run when #972 is fixed
    // Duplicate of i972 in pos/idempotentcalls
    Math.sqrt(3)
    java.util.Arrays.asList(1, 2, 3)
  }

  def reg2(): Unit = {
    lazy val foo: Stream[Int] = 1 #:: foo
    foo(2)
  }

}

object Test {

  def main(args: Array[String]) = {

    val a = new A
    import a._

    test1()
    test2()
    test3()
    test4()
    test5()
/*    test6() // inner functions
    test6bis()*/
    test7()
    test8(new A)
    test9()
    test10()
/*    test10()
    test11()
    test11bis()*/
    //test12()
    test13()
    test14()
    test15()
    test16()
    test17()
    test18()
    test19()
    test20()
    test21()
    test23(true)
    test23(false)
    test24(true)
    test24(false)
    test25("Hello") // inner functions
    test25(1)       // inner functions
    test26()
    test27()
    test28() // inner functions
    test29() // inner functions
    test30()
    test31()
    test32()
    test33()
    test34NotOptimizable()
    test35() // inner functions
    test36() // inner functions
    test37() // inner functions

    // Regression tests
    reg1()
    reg2()
  }
}
