package test

import scala.annotation.Idempotent

object CommonSubexpression {

  @Idempotent def sum(i1: Int, i2: Int) = i1 + i2

  def method1: Int = {
    val a = 1
    val c = sum(sum(1, a), 3)
    val d = sum(sum(1, a), 4)
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

  def main(args: Array[String]): Unit = {
    println("executing")
    assert(method1 == 1)
    assert(method2 == 1)
  }

}
