module Happle

import Nope

%access public export
%default total

data HappleKeyword
  = LambdaDot
  | Name String
  --| NameLet
  --| TypeDecl

tokenize : String -> HappleKeyword
tokenize "." = LambdaDot
tokenize x = Name x
