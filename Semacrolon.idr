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

parseMacro : NopeAst -> SemacrolonAst
parseMacro (TermAst x) = ?parseMacro_rhs_1
parseMacro (Appl ast ast_ xs) = ?parseMacro_rhs_2

execMacro : SemacrolonAst -> NopeAst
execMacro (MacroDef x xs ast) = ?execMacro_rhs_1
execMacro (MacroExpr x) = ?execMacro_rhs_2

