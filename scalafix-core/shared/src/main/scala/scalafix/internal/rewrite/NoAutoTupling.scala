package scalafix.internal.rewrite

import scala.meta._
import scalafix.Patch
import scalafix.SemanticCtx
import scalafix.rewrite.RewriteCtx
import scalafix.rewrite.SemanticRewrite

case class NoAutoTupling(semanticCtx: SemanticCtx)
    extends SemanticRewrite(semanticCtx) {

  private[this] def addWrappingParens(ctx: RewriteCtx, args: Seq[Term]): Patch =
    ctx.addLeft(args.head.tokens.head, "(") +
      ctx.addRight(args.last.tokens.last, ")")

  override def rewrite(ctx: RewriteCtx): Patch = {
    val adaptations = semanticCtx.messages.toIterator.collect {
      case Message(pos, _, msg)
          if msg.startsWith("Adapting argument list by creating a") =>
        pos
    }.toSet

    ctx.tree.collect {
      case t: Term.Apply if adaptations.contains(t.pos) =>
        addWrappingParens(ctx, t.args)
    }.asPatch
  }
}
