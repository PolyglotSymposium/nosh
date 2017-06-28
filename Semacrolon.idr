module Semacrolon

import Nope

%access public export
%default total

--data SemacrolonToken : Type where
--  STMacro : SemacrolonToken
--  STEq : SemacrolonToken
--  STMacroName : String -> SemacrolonToken
--  STTerm : Term String -> SemacrolonToken

data SemacrolonExpr : Type where
  MacroAppl : String -> List SemacrolonExpr -> SemacrolonExpr
  NopeAppl : Term String -> SemacrolonExpr -> List SemacrolonExpr -> SemacrolonExpr
  SemacrolonTerm : Term String -> SemacrolonExpr

data SemacrolonAst : Type where
  MacroDef : String -> List SemacrolonExpr -> NopeAst -> SemacrolonAst
  MacroExpr : SemacrolonExpr -> SemacrolonAst

mutual
  -- This is necessary for totality
  unwrapQuotedIds_ : List NopeAst -> List NopeAst
  unwrapQuotedIds_ [] = []
  unwrapQuotedIds_ (ast :: asts) = unwrapQuotedIds ast :: unwrapQuotedIds_ asts

  unwrapQuotedIds : NopeAst -> NopeAst
  unwrapQuotedIds (TermAst (Raw '#' y)) = TermAst (Id y)
  unwrapQuotedIds (TermAst term@(Raw _ _)) = TermAst term
  unwrapQuotedIds (TermAst term@(Id _)) = TermAst term
  unwrapQuotedIds (Appl ast ast_ asts) =
    Appl (unwrapQuotedIds ast) (unwrapQuotedIds ast_) (unwrapQuotedIds_ asts)

parseMacroExpr : NopeAst -> Maybe SemacrolonExpr
parseMacroExpr (TermAst term@(Raw _ _)) = Just $ SemacrolonTerm term
parseMacroExpr (TermAst (Id x)) =
  case unpack x of
    ('#' :: _) => Nothing
    (';' :: _) => Just $ MacroAppl x []
    _ =>  Just $ SemacrolonTerm $ Id x
parseMacroExpr (Appl (TermAst x) ast2 xs) = ?parseMacroExpr_rhs_1
parseMacroExpr (Appl (Appl ast ast_ ys) ast2 xs) = ?parseMacroExpr_rhs_3

parseMacro : NopeAst -> Maybe SemacrolonAst

execMacro : SemacrolonAst -> NopeAst
execMacro (MacroDef x xs ast) = ?execMacro_rhs_1
execMacro (MacroExpr x) = ?execMacro_rhs_2

