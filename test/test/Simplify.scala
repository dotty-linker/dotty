package test

import org.junit.{Assert, Test}

class Simplify extends DottyTest {

  val sourceCode = s"""
     |package varifytest
     |
     |object A {
     |def main(args: Array[String]) = {
     |def mutableMe(a: Int): Int = {
     |var b: Int = a: Int
     |b = b + 2
     |b * 3
     |}
     |
     |def mutableMe2(a: Int): Int = {
     |var b = a + 1
     |b += 2
     |b * 3
     |}
     |
     |println(mutableMe(5))
     |println(mutableMe2(5))
     |}
     |}
   """.stripMargin

  @Test
  def varify = {
    checkCompile("simplify", sourceCode){ (tree, context) =>
      implicit val ctx = context
      println(tree.show)
      Assert.assertTrue("the varify optimization does not work correctly",
        tree.show.contains(
          s"""|def mutableMe(var a: Int): Int = {
              |  a = a.+(2)
              |  a.*(3)
              |}
              |def mutableMe2(var a: Int): Int = {
              |  a = a.+(1)
              |  a = a.+(2)
              |  a.*(3)
              |}
         """.stripMargin.trim
        )
      )
    }
  }

}
