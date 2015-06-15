module Syntax.Infix where

  open import Sets.Enumerated using (Bool; true; false)

  -- Can be infix, infixl or infixr:
  infixr 3 _+_
  data BinTree' : Set where
    x : BinTree'
    _+_ : BinTree' → BinTree' → BinTree'

  tree₁ : BinTree'
  tree₁ = x + x + x -- x + (x + (x))
