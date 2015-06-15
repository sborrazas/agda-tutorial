module Functions.Functions_vs_Sets where

  open import Sets.Enumerated using (Bool; true; false)

  data Not : Bool → Bool → Set where
    n₁ : Not true false
    n₂ : Not false true
