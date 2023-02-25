import Lean.Parser.Extension
import Lean.PrettyPrinter.Parenthesizer
import Lean.PrettyPrinter.Formatter

open Lean
open Lean.Parser

abbrev singleQuotedStrKind : SyntaxNodeKind := `sqstr
abbrev SingleQuotedStr := TSyntax singleQuotedStrKind

private partial def singleQuotedStrAuxAux (startPos : String.Pos) : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if h : input.atEnd i then s.mkUnexpectedErrorAt "unterminated single quoted string literal" startPos
  else
    let curr := input.get' i h
    let s    := s.setPos (input.next' i h)
    if curr == '\'' then
      mkNodeToken singleQuotedStrKind startPos c s
    else if curr == '\\' then andthenFn quotedCharFn (singleQuotedStrAuxAux startPos) c s
    else singleQuotedStrAuxAux startPos c s

private def singleQuotedStrAux : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  let curr  := input.get i
  if curr == '\'' then
    singleQuotedStrAuxAux i c (s.next input i)
  else
    let initStackSz := s.stackSize
    s.mkErrorsAt ["single quoted string"] i initStackSz

private def updateTokenCache (startPos : String.Pos) (s : ParserState) : ParserState :=
  -- do not cache token parsing errors, which are rare and usually fatal and thus not worth an extra field in `TokenCache`
  match s with
  | ⟨stack, lhsPrec, pos, ⟨_, catCache⟩, none⟩ =>
    if stack.size == 0 then s
    else
      let tk := stack.back
      ⟨stack, lhsPrec, pos, ⟨{ startPos := startPos, stopPos := pos, token := tk }, catCache⟩, none⟩
  | other => other

def singleQuotedStrFn (expected : List String := []) : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if input.atEnd i then s.mkEOIError expected
  else
    let tkc := s.cache.tokenCache
    if tkc.startPos == i then
      let s := s.pushSyntax tkc.token
      s.setPos tkc.stopPos
    else
      let s := singleQuotedStrAux c s
      updateTokenCache i s

def singleQuotedStrNoAntiquot : Parser := {
  fn   := singleQuotedStrFn
  info := mkAtomicInfo "singleQuoted"
}

namespace Lean.Syntax

partial def decodeSingleQuotedStrLitAux (s : String) (i : String.Pos) (acc : String) : Option String := do
  let c := s.get i
  let i := s.next i
  if c == '\'' then
    pure acc
  else if s.atEnd i then
    none
  else if c == '\\' then do
    let (c, i) ← decodeQuotedChar s i
    decodeSingleQuotedStrLitAux s i (acc.push c)
  else
    decodeSingleQuotedStrLitAux s i (acc.push c)

def decodeSingleQuotedStrLit (s : String) : Option String :=
  decodeSingleQuotedStrLitAux s ⟨1⟩ ""

def isSingleQuotedStr? (stx : Syntax) : Option String :=
  match isLit? singleQuotedStrKind stx with
  | some val => decodeSingleQuotedStrLit val
  | _        => none

def getSingleQuotedStr (s : SingleQuotedStr) : String :=
  s.raw.isSingleQuotedStr?.getD ""

@[combinator_formatter singleQuotedStrNoAntiquot] def singleQuotedStrNoAntiquot.formatter := PrettyPrinter.Formatter.visitAtom singleQuotedStrKind
@[combinator_parenthesizer singleQuotedStrNoAntiquot] def singleQuotedStrNoAntiquot.parenthesizer := PrettyPrinter.Parenthesizer.visitToken