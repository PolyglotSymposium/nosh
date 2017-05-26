module Nope

%default total
%access public export

data Token a
  = Identifier a
  | InfixId a
  | Raw a
--  | Indent
--  | Newline

Functor Token where
  map f (Identifier x) = Identifier (f x)
  map f (InfixId x) = InfixId (f x)
  map f (Raw x) = Raw (f x)

identifier : Token a -> Maybe a
identifier (Identifier x) = Just x
identifier _ = Nothing

infixId : Token a -> Maybe a
infixId (InfixId x) = Just x
infixId _ = Nothing

insert : Char -> Token (List Char) -> Token (List Char)
insert c (Identifier cs) = Identifier (c :: cs)
insert c (InfixId cs) = InfixId (c :: cs)
insert c (Raw cs) = Raw (c :: cs)

mutual
  tokenizeRaw : Char -> Token (List Char) -> List Char -> List (Token (List Char))
  tokenizeRaw final t [] = [t]
  tokenizeRaw final t (c :: []) = [insert c t]
  tokenizeRaw final t (c :: (')' :: cs)) =
    if final == c
    then t :: tokenize' cs
    else tokenizeRaw final (insert ')' $ insert c t) cs
  tokenizeRaw final t (c :: cs@(_ :: _)) =
     tokenizeRaw final (insert c t) cs

  tokenizeWord : Token (List Char) -> List Char -> List (Token (List Char))
  tokenizeWord t [] = [t]
  tokenizeWord t (' ' :: cs) = t :: tokenize' cs
  tokenizeWord t (c :: cs) = tokenizeWord (insert c t) cs

  tokenize' : List Char -> List (Token (List Char))
  tokenize' [] = []
  tokenize' (c :: []) = [if isAlphaNum c then Identifier [c] else InfixId [c]]
  tokenize' ('(' :: (c :: cs)) = tokenizeRaw c (Raw []) cs
  tokenize' (' ' :: cs@(_ :: _)) = tokenize' cs
  tokenize' ('_' :: cs@(_ :: _)) = tokenizeWord (Identifier ['_']) cs
  tokenize' (c :: cs@(_ :: _)) =
    if isAlphaNum c
    then tokenizeWord (Identifier [c]) cs
    else tokenizeWord (InfixId [c]) cs


tokenize : String -> List (Token String)
tokenize = map (map (pack . reverse)) . tokenize' . unpack

public export
data NopeAst : Type where
  RawTerm : String -> NopeAst
  IdTerm : String -> NopeAst
  Appl : NopeAst -> NopeAst -> List NopeAst -> NopeAst

%name NopeAst ast, ast_, ast'

data Terms : Type where
  AllTerms : NopeAst -> List NopeAst -> Terms
  TermsAndThen : NopeAst -> List NopeAst -> String -> NopeAst -> Terms

consIdTerm : String -> Terms -> Terms
consIdTerm x (AllTerms a as) = AllTerms (IdTerm x) (a :: as)
consIdTerm x (TermsAndThen a as y a_) = TermsAndThen (IdTerm x) (a :: as) y a_

consRawTerm : String -> Terms -> Terms
consRawTerm x (AllTerms a as) = AllTerms (RawTerm x) (a :: as)
consRawTerm x (TermsAndThen a as y a_) = TermsAndThen (RawTerm x) (a :: as) y a_

mutual
  terms : (l : List (Token String)) -> { auto p : NonEmpty l } -> Terms
  terms [] {p} impossible
  terms ((Identifier x) :: []) = AllTerms (IdTerm x) []
  terms ((Identifier x) :: xs@(_ :: _)) = consIdTerm x $ terms xs
  terms ((Raw x) :: []) = AllTerms (RawTerm x) []
  terms ((Raw x) :: xs@(_ :: _)) = consRawTerm x $ terms xs
  terms ((Identifier x) :: ((InfixId y) :: xs@(_ :: _))) = TermsAndThen (IdTerm x) [] y $ parse xs
  terms ((Raw x) :: ((InfixId y) :: xs@(_ :: _))) = TermsAndThen (RawTerm x) [] y $ parse xs
  terms ((InfixId x) :: []) = AllTerms (IdTerm x) []
  terms ((InfixId x) :: xs@(_ :: _)) = consIdTerm x $ terms xs
  terms ((Raw x) :: xs@(_ :: _)) = consRawTerm x $ terms xs

  parse_ : String -> List (Token String) -> NopeAst
  parse_ i [] = IdTerm i
  parse_ i ts@((Identifier x) :: _) =
    case terms ts of
      (AllTerms ast asts) =>
        Appl (IdTerm i) ast asts
      (TermsAndThen ast asts ii a) =>
        Appl (IdTerm ii) (Appl (IdTerm i) ast asts) [a]
  parse_ i ts@((Raw x) :: _) =
    case terms ts of
      (AllTerms ast asts) =>
        Appl (RawTerm i) ast asts
      (TermsAndThen ast asts ii a) =>
        Appl (RawTerm ii) (Appl (RawTerm i) ast asts) [a]
  parse_ i ((InfixId ii) :: []) =
    Appl (IdTerm i) (IdTerm ii) []
  parse_ i ((InfixId ii) :: ts@(_ :: _)) =
    Appl (IdTerm ii) (IdTerm i) [parse ts]
  parse_ i ((Raw ii) :: []) =
    Appl (RawTerm i) (RawTerm ii) []
  parse_ i ((Raw ii) :: ts@(_ :: _)) =
    Appl (RawTerm ii) (RawTerm i) [parse ts]

  parse : (l : List (Token String)) -> { auto p : NonEmpty l } -> NopeAst
  parse [] {p} impossible
  parse ((Identifier i) :: ts) = parse_ i ts
  parse ((InfixId i) :: ts) = parse_ i ts
  parse ((Raw i) :: ts) = parse_ i ts

export
parseNope : String -> Maybe NopeAst
parseNope ts =
  case tokenize ts of
    [] => Nothing
    (t :: ts') => Just $ parse $ t :: ts'

