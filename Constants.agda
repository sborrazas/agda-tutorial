module Constants where

  open import Sets.Enumerated using (Bool; true; false)
  open import Sets.Recursive using (ℕ; zero; suc)

  nine : ℕ
  nine = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

  ten : ℕ
  ten = suc nine
