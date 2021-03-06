package scalafix.rewrite

import scalafix._
import scalafix.internal.config._
import metaconfig.ConfError
import metaconfig.Configured

object ConfigRewrite {
  def apply(
      patches: ConfigRewritePatches,
      getSemanticCtx: LazySemanticCtx): Configured[Option[Rewrite]] = {
    val configurationPatches = patches.all
    if (configurationPatches.isEmpty) Configured.Ok(None)
    else {
      getSemanticCtx(RewriteKind.Semantic) match {
        case None =>
          ConfError
            .msg(".scalafix.conf patches require the Semantic API.")
            .notOk
        case Some(semanticCtx) =>
          val rewrite = Rewrite.constant(
            ".scalafix.conf",
            configurationPatches.asPatch,
            semanticCtx
          )
          Configured.Ok(Some(rewrite))
      }
    }
  }

}
