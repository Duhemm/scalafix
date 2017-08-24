package scalafix.internal.rewrite

import scala.meta._
import scala.meta.tokens.Token.LeftParen
import scala.meta.tokens.Token.RightParen
import scalafix._
import scalafix.rewrite.RewriteCtx
import scalafix.rewrite.SemanticRewrite

case class Sbt1(sctx: SemanticCtx) extends SemanticRewrite(sctx) {

  private def infoStartsWith(atPos: Position, prefix: String): Boolean =
    sctx
      .symbol(atPos)
      .flatMap(sctx.denotation)
      .exists(denot => denot.info.startsWith(prefix))

  private def existKeys(lhs: Term, typePrefix: String): Boolean = {
    val singleNames = lhs match {
      case tn @ Term.Name(name) =>
        // Workaround for scalameta/scalameta#1083. We drop the parentheses
        // if tn is `(someName)`.
        val pos =
          if (tn.pos.text.startsWith("(") && tn.pos.text.endsWith(")")) {
            tn.tokens.tail.head.pos
          } else {
            tn.pos
          }

        if (infoStartsWith(pos, typePrefix)) tn :: Nil
        else Nil
      case _ => Nil
    }
    val scopedNames = lhs.collect {
      case Term.Select(tn @ Term.Name(name), Term.Name("in"))
          if infoStartsWith(tn.pos, typePrefix) =>
        name
      case Term.ApplyInfix(tn @ Term.Name(name), Term.Name("in"), _, _)
          if infoStartsWith(tn.pos, typePrefix) =>
        name
    }
    (singleNames ++ scopedNames).nonEmpty
  }

  override def rewrite(ctx: RewriteCtx): Patch = {
    sealed abstract class SbtOperator {
      val operator: String
      val newOperator: String

      def unapply(tree: Term): Option[(Term, Token, Term)] = tree match {
        case Term.ApplyInfix(lhs, o @ Term.Name(`operator`), _, Seq(rhs)) =>
          Some((lhs, o.tokens.head, rhs))
        case Term
              .Apply(Term.Select(lhs, o @ Term.Name(`operator`)), Seq(rhs)) =>
          Some((lhs, o.tokens.head, rhs))
        case Term.Apply(
            Term.ApplyType(Term.Select(lhs, o @ Term.Name(`operator`)), _),
            Seq(rhs)) =>
          Some((lhs, o.tokens.head, rhs))
        case _ =>
          None
      }

      private def wrapInParenthesis(tokens: Tokens): List[Patch] =
        List(ctx.addLeft(tokens.head, "("), ctx.addRight(tokens.last, ")"))

      private def isParensWrapped(tokens: Tokens): Boolean = {
        tokens.head.isInstanceOf[LeftParen] &&
        tokens.last.isInstanceOf[RightParen]
      }

      def rewriteDslOperator(
          lhs: Term,
          opToken: Token,
          rhs: Term): List[Patch] = {
        val wrapExpression = rhs match {
          case arg @ Term.Apply(_, Seq(_: Term.Block))
              if !isParensWrapped(arg.tokens) =>
            wrapInParenthesis(arg.tokens)
          case arg: Term.ApplyInfix if !isParensWrapped(arg.tokens) =>
            wrapInParenthesis(arg.tokens)
          case _ => Nil
        }

        val removeOperator = ctx.removeToken(opToken)
        val addNewOperator = ctx.addLeft(opToken, newOperator)
        val rewriteRhs = {
          val requiresEvaluated = existKeys(lhs, SbtTypes.inputKey)
          val newSelector =
            if (requiresEvaluated) SbtSelectors.evaluated
            else SbtSelectors.value
          ctx.addRight(rhs.tokens.last, newSelector)
        }

        (removeOperator :: addNewOperator :: wrapExpression) ++ Seq(rewriteRhs)
      }
    }

    object SbtSelectors {
      val value = ".value"
      val evaluated = ".evaluated"
    }

    object SbtTypes {
      val inputKey: String = "sbt.InputKey["
    }

    object `<<=` extends SbtOperator {
      override final val operator = "<<="
      override final val newOperator: String = ":="
    }

    object `<+=` extends SbtOperator {
      override final val operator = "<+="
      override final val newOperator: String = "+="
    }

    object `<++=` extends SbtOperator {
      override final val operator = "<++="
      override final val newOperator: String = "++="
    }

    object `map` extends SbtOperator {
      private var tupleSyntaxImported = false
      override final val operator = "map"
      override final val newOperator: String = "map"

      override def rewriteDslOperator(
          lhs: Term,
          opToken: Token,
          rhs: Term): List[Patch] = lhs match {
        case Term.Tuple(args) if !tupleSyntaxImported =>
          tupleSyntaxImported = true
          ctx.addGlobalImport(importer"sbt.TupleSyntax._") :: Nil
        case _ =>
          Nil
      }
    }

    object `value` {
      def unapply(tree: Term): Option[(Term, Token)] = tree match {
        case Term.Select(lhs, o @ Term.Name("value"))
            if existKeys(lhs, SbtTypes.inputKey) =>
          Some((lhs, o.tokens.head))
        case _ =>
          None
      }

      def rewriteSelector(lhs: Term, selToken: Token): List[Patch] = {
        ctx.replaceToken(selToken, "evaluated") :: Nil
      }
    }

    ctx.tree
      .collect {
        case `<<=`(lhs: Term, opToken: Token, rhs: Term) =>
          `<<=`.rewriteDslOperator(lhs, opToken, rhs)
        case `<+=`(lhs: Term, opToken: Token, rhs: Term) =>
          `<+=`.rewriteDslOperator(lhs, opToken, rhs)
        case `<++=`(lhs: Term, opToken: Token, rhs: Term) =>
          `<++=`.rewriteDslOperator(lhs, opToken, rhs)
        case `map`(lhs: Term, opToken: Token, rhs: Term) =>
          `map`.rewriteDslOperator(lhs, opToken, rhs)
        case `value`(lhs: Term, selToken: Token) =>
          `value`.rewriteSelector(lhs, selToken)
        case tpe @ t"sbt.inc.Analysis" =>
          // scala.meta bug???
          val ttpe = tpe.asInstanceOf[Type.Select]
          sctx.symbol(ttpe.name.pos).map {
            case sym: Symbol.Global =>
              ctx.renameSymbol(sym, "xsbti.compile.CompileAnalysis")
            case x =>
              Patch.empty
          }.toList
      }
      .flatten
      .asPatch
  }
}
