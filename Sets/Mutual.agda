module Sets.Mutual where

  open import Sets.Enumerated using (Bool; true; false)
  open import Syntax.Decimal_Naturals using (ℕ; zero; suc)

  data L : Set
  data M : Set

  data L where
    nil : L
    _∷_ : ℕ → M → L

  data M where
    _∷_ : Bool → L → M

  infix 3 _+_
  infix 5 _*_
  data MyGrammar : Set where
    num : ℕ         → MyGrammar
    _+_ : MyGrammar → MyGrammar → MyGrammar
    _*_ : MyGrammar → MyGrammar → MyGrammar
