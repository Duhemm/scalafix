package scalafix.tests

import scalafix.SemanticCtx
import scalafix.reflect.ScalafixReflect
import metaconfig.Conf
import org.scalatest.FunSuite

class URLConfiguration extends FunSuite {
  import scalafix.internal.config.ScalafixConfig
  val url =
    "https://gist.githubusercontent.com/olafurpg/fc6f43a695ac996bd02000f45ed02e63/raw/193f22e4e2aa624c90fe2ac3bb530b025e104a69/ExampleRewrite.scala"
  test("compile from URL works") {

    val semanticCtx = Some(SemanticCtx(Nil))
    val obtained =
      ScalafixReflect
        .fromLazySemanticCtx(_ => semanticCtx)
        .read(Conf.Str(url))
    assert(obtained.get.name.contains("Rewrite2"))
  }
}
