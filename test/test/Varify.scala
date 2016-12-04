package test

object A {
  def main(args: Array[String]) = {
    def mutableMe(a: Int): Int = {
      var b: Int = a: Int
      b = b + 2
      b * 3
      }

    def mutableMe2(a: Int): Int = {
      var b = a + 1
      b += 2
      b * 3
      }

    println(mutableMe(5))
    println(mutableMe2(5))
  }
}
