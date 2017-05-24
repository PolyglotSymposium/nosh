module Nope

%default total

data Token
  = Identifier String
  | InfixId String
--  | Indent
--  | Newline

identifier : Token -> Maybe String
identifier (Identifier x) = Just x
identifier _ = Nothing

infixId : Token -> Maybe String
infixId (InfixId x) = Just x
infixId _ = Nothing

isInfixed : String -> Bool
isInfixed = not . foldr (\x => \y => x && y) True . map isAlphaNum . unpack

idPossiblyInfixed : String -> Token
idPossiblyInfixed x = if isInfixed x then InfixId x else Identifier x

tokenize : String -> List Token
tokenize = map idPossiblyInfixed . words

public export
data NopeAst : Type where
  Term : String -> NopeAst
  Appl : NopeAst -> NopeAst -> List NopeAst -> NopeAst

%name NopeAst ast, ast_, ast'

data Terms : Type where
  AllTerms : NopeAst -> List NopeAst -> Terms
  TermsAndThen : NopeAst -> List NopeAst -> String -> NopeAst -> Terms

consTerm : String -> Terms -> Terms
consTerm x (AllTerms a as) = AllTerms (Term x) (a :: as)
consTerm x (TermsAndThen a as y a_) = TermsAndThen (Term x) (a :: as) y a_

mutual
  terms : (l : List Token) -> { auto p : NonEmpty l } -> Terms
  terms [] {p} impossible
  terms ((Identifier x) :: []) = AllTerms (Term x) []
  terms ((Identifier x) :: xs@((Identifier _) :: _)) = consTerm x $ terms xs
  terms ((Identifier x) :: xs@((InfixId _) :: [])) = consTerm x $ terms xs
  terms ((Identifier x) :: ((InfixId y) :: xs@(_ :: _))) = TermsAndThen (Term x) [] y $ parse xs
  terms ((InfixId x) :: []) = AllTerms (Term x) []
  terms ((InfixId x) :: xs@(_ :: _)) = consTerm x $ terms xs

  parse_ : String -> List Token -> NopeAst
  parse_ i [] = Term i
  parse_ i ts@((Identifier x) :: _) =
    case terms ts of
      (AllTerms ast asts) =>
        Appl (Term i) ast asts
      (TermsAndThen ast asts ii a) =>
        Appl (Term ii) (Appl (Term i) ast asts) [a]
  parse_ i ((InfixId ii) :: []) =
    Appl (Term i) (Term ii) []
  parse_ i ((InfixId ii) :: ts@(_ :: _)) =
    Appl (Term ii) (Term i) [parse ts]

  parse : (l : List Token) -> { auto p : NonEmpty l } -> NopeAst
  parse [] {p} impossible
  parse ((Identifier i) :: ts) = parse_ i ts
  parse ((InfixId i) :: ts) = parse_ i ts

export
parseNope : String -> Maybe NopeAst
parseNope ts =
  case tokenize ts of
    [] => Nothing
    (t :: ts') => Just $ parse $ t :: ts'

