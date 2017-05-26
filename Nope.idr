module Nope

%default total
%access public export

data Term a
  = Raw Char a
  | Id a

Functor Term where
  map f (Raw c x) = Raw c (f x)
  map f (Id x) = Id (f x)

data Token a
  = NonInfix (Term a)
  | InfixId a
--  | Indent
--  | Newline

Functor Token where
  map f (NonInfix x) = NonInfix (map f x)
  map f (InfixId x) = InfixId (f x)

mutual
  tokenizeRaw : Char -> List Char -> List Char -> List (Token (List Char))
  tokenizeRaw final t [] = [NonInfix (Raw final t)]
  tokenizeRaw final t (c :: []) = [NonInfix (Raw final (c :: t))]
  tokenizeRaw final t (c :: (')' :: cs)) =
    if final == c
    then (NonInfix (Raw final t)) :: tokenize' cs
    else tokenizeRaw final (')' :: c :: t) cs
  tokenizeRaw final t (c :: cs@(_ :: _)) =
     tokenizeRaw final (c :: t) cs

  tokenizeWord : (List Char -> Token (List Char)) -> List Char -> List Char -> List (Token (List Char))
  tokenizeWord ctr t [] = [ctr t]
  tokenizeWord ctr t (' ' :: cs) = ctr t :: tokenize' cs
  tokenizeWord ctr t (c :: cs) = tokenizeWord ctr (c :: t) cs

  tokenize' : List Char -> List (Token (List Char))
  tokenize' [] = []
  tokenize' (c :: []) = [if isAlphaNum c then NonInfix (Id [c]) else InfixId [c]]
  tokenize' ('(' :: (c :: cs)) = tokenizeRaw c [] cs
  tokenize' (' ' :: cs@(_ :: _)) = tokenize' cs
  tokenize' ('_' :: cs@(_ :: _)) = tokenizeWord (NonInfix . Id) ['_'] cs
  tokenize' (c :: cs@(_ :: _)) =
    if isAlphaNum c
    then tokenizeWord (NonInfix . Id) [c] cs
    else tokenizeWord InfixId [c] cs


tokenize : String -> List (Token String)
tokenize = map (map (pack . reverse)) . tokenize' . unpack

public export
data NopeAst : Type where
  TermAst : Term String -> NopeAst
  Appl : NopeAst -> NopeAst -> List NopeAst -> NopeAst

%name NopeAst ast, ast_, ast'

data Terms : Type where
  AllTerms : NopeAst -> List NopeAst -> Terms
  TermsAndThen : NopeAst -> List NopeAst -> String -> NopeAst -> Terms

consTerm : Term String -> Terms -> Terms
consTerm x (AllTerms a as) = AllTerms (TermAst x) (a :: as)
consTerm x (TermsAndThen a as y a_) = TermsAndThen (TermAst x) (a :: as) y a_

mutual
  terms : (l : List (Token String)) -> { auto p : NonEmpty l } -> Terms
  terms [] {p} impossible
  terms ((NonInfix x) :: []) = AllTerms (TermAst x) []
  terms ((NonInfix x) :: ((InfixId y) :: xs@(_ :: _))) = TermsAndThen (TermAst x) [] y $ parse xs
  terms ((NonInfix x) :: xs@(_ :: _)) = consTerm x $ terms xs
  terms ((InfixId x) :: []) = AllTerms (TermAst (Id x)) []
  terms ((InfixId x) :: xs@(_ :: _)) = consTerm (Id x) $ terms xs

  parse_ : Term String -> List (Token String) -> NopeAst
  parse_ i [] = TermAst i
  parse_ i ((InfixId ii) :: []) =
    Appl (TermAst i) (TermAst (Id ii)) []
  parse_ i ((InfixId ii) :: ts@(_ :: _)) =
    Appl (TermAst (Id ii)) (TermAst i) [parse ts]
  parse_ i ts@(_ :: _) =
    case terms ts of
      (AllTerms ast asts) =>
        Appl (TermAst i) ast asts
      (TermsAndThen ast asts ii a) =>
        Appl (TermAst (Id ii)) (Appl (TermAst i) ast asts) [a]

  parse : (l : List (Token String)) -> { auto p : NonEmpty l } -> NopeAst
  parse [] {p} impossible
  parse ((NonInfix i) :: ts) = parse_ i ts
  parse ((InfixId i) :: ts) = parse_ (Id i) ts

export
parseNope : String -> Maybe NopeAst
parseNope ts =
  case tokenize ts of
    [] => Nothing
    (t :: ts') => Just $ parse $ t :: ts'

