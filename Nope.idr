module Nope

%access public export
%default total

data Token
  = Identifier String
--  | Indent
--  | Newline

tokenize : String -> List Token
tokenize = map Identifier . words

data Ast : Type where
  Term : String -> Ast
  Appl : Ast -> List Ast -> Ast

parse : (l : List Token) -> { auto p : NonEmpty l } -> Ast
parse [] {p} impossible
parse ((Identifier x) :: []) = Term x
parse ((Identifier x) :: xs@(_ :: _)) =
  Appl (Term x) $ map (\(Identifier x) => Term x) xs

exec : String -> Maybe Ast
exec ts =
  case tokenize ts of
    [] => Nothing
    (t :: ts') => Just $ parse $ t :: ts'
