package scalafix.internal.rewrite

import scala.collection.immutable.Seq
import scala.meta._
import scala.meta.contrib._
import scala.meta.internal.scalafix.ScalafixScalametaHacks
import scalafix.Patch
import scalafix.SemanticCtx
import scalafix.internal.config.MemberKind
import scalafix.internal.config.MemberVisibility
import scalafix.rewrite.RewriteCtx
import scalafix.rewrite.SemanticRewrite
import scalafix.syntax._
import scalafix.util.TokenOps

case class ExplicitReturnTypes(semanticCtx: SemanticCtx)
    extends SemanticRewrite(semanticCtx) {
  // Don't explicitly annotate vals when the right-hand body is a single call
  // to `implicitly`. Prevents ambiguous implicit. Not annotating in such cases,
  // this a common trick employed implicit-heavy code to workaround SI-2712.
  // Context: https://gitter.im/typelevel/cats?at=584573151eb3d648695b4a50
  private def isImplicitly(term: Term): Boolean = term match {
    case Term.ApplyType(Term.Name("implicitly"), _) => true
    case _ => false
  }

  def defnName(defn: Defn): Option[Name] = Option(defn).collect {
    case Defn.Val(_, Seq(Pat.Var(name)), _, _) => name
    case Defn.Var(_, Seq(Pat.Var(name)), _, _) => name
    case Defn.Def(_, name, _, _, _, _) => name
  }

  def visibility(mods: Traversable[Mod]): MemberVisibility =
    mods
      .collectFirst {
        case _: Mod.Private => MemberVisibility.Private
        case _: Mod.Protected => MemberVisibility.Protected
      }
      .getOrElse(MemberVisibility.Public)

  def kind(defn: Defn): Option[MemberKind] = Option(defn).collect {
    case _: Defn.Val => MemberKind.Val
    case _: Defn.Def => MemberKind.Def
    case _: Defn.Var => MemberKind.Var
  }

  def parseDenotationInfo(denot: Denotation): Option[Type] = {
    val base =
      if (denot.isVal || denot.isVar) denot.info
      else if (denot.isDef) denot.info.replaceFirst(".*\\)", "")
      else {
        throw new UnsupportedOperationException(
          s"Can't parse type for denotation $denot, denot.info=${denot.info}")
      }
    if (denot.isVal || denot.isDef)
      base.parse[Type].toOption
    else
      /*
    Currently a symbol of Var points to its setter function.
    That's why its argument type should be extracted via pattern-match.
       */
      for {
        stat <- base.parse[Stat].toOption
        typ <- stat.collectFirst { case Term.Ascribe(_, typ) => typ }
      } yield typ
  }

  def defnType(defn: Defn): Option[Type] =
    for {
      name <- defnName(defn)
      symbol <- name.symbol
      denot <- symbol.denotation
      typ <- parseDenotationInfo(denot)
    } yield typ

  override def rewrite(ctx: RewriteCtx): Patch = {
    import scala.meta._
    import ctx._
    def fix(defn: Defn, body: Term): Seq[Patch] = {
      import ctx.tokenList._
      for {
        start <- defn.tokens.headOption
        end <- body.tokens.headOption
        // Left-hand side tokens in definition.
        // Example: `val x = ` from `val x = rhs.banana`
        lhsTokens = slice(start, end)
        replace <- lhsTokens.reverseIterator.find(x =>
          !x.is[Token.Equals] && !x.is[Trivia])
        typ <- defnType(defn)
        space = {
          if (TokenOps.needsLeadingSpaceBeforeColon(replace)) " "
          else ""
        }
      } yield ctx.addRight(replace, s"$space: ${treeSyntax(typ)}")
    }.to[Seq]

    def treeSyntax(tree: Tree): String =
      ScalafixScalametaHacks.resetOrigin(tree).syntax

    def isRewriteCandidate[D <: Defn](
        defn: D,
        mods: Traversable[Mod],
        body: Term)(implicit ev: Extract[D, Mod]): Boolean = {
      import ctx.config.explicitReturnTypes._

      def matchesMemberVisibility(): Boolean =
        memberVisibility.contains(visibility(mods))

      def matchesMemberKind(): Boolean =
        kind(defn).exists(memberKind.contains)

      def matchesSimpleDefinition(): Boolean =
        body.is[Lit] && skipSimpleDefinitions

      defn.hasMod(mod"implicit") && !isImplicitly(body) ||
      !defn.hasMod(mod"implicit") &&
      !matchesSimpleDefinition() &&
      matchesMemberKind() &&
      matchesMemberVisibility()
    }

    tree
      .collect {
        case t @ Defn.Val(mods, _, None, body)
            if isRewriteCandidate(t, mods, body) =>
          fix(t, body)

        case t @ Defn.Var(mods, _, None, Some(body))
            if isRewriteCandidate(t, mods, body) =>
          fix(t, body)

        case t @ Defn.Def(mods, _, _, _, None, body)
            if isRewriteCandidate(t, mods, body) =>
          fix(t, body)
      }
      .flatten
      .asPatch
  }
}
