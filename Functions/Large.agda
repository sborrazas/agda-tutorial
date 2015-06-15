module Functions.Large where

  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Empty using (⊥)
  open import Data.Unit using (⊤; tt)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Sets.Enumerated using (Bool; true; false)

  data  _≤_ : ℕ → ℕ → Set where
    z≤n : {n : ℕ} →               zero  ≤ n
    s≤s : {m n : ℕ} →   m ≤ n  →  suc m ≤ suc n

  _≤′_ : ℕ → ℕ → Set
  zero  ≤′ n     = ⊤
  suc m ≤′ zero  = ⊥
  suc m ≤′ suc n = m ≤′ n

  f : {n m : ℕ} → n ≤ m → n ≤ suc m
  f z≤n = z≤n
  f (s≤s x) = s≤s (f x)

  f′ : {n m : ℕ} → n ≤′ m → n ≤′ suc m
  f′ {zero} {m} tt = tt
  f′ {suc n} {zero} ()
  f′ {suc n} {suc m} x = f′ {n} {m} x

  -- Give recursive definitions for _≡_ and _≢_ on natural numbers!
  _≡_ : ℕ → ℕ → Set
  zero ≡ zero = ⊤
  (suc n) ≡ zero = ⊥
  zero ≡ (suc n) = ⊥
  (suc n) ≡ (suc m) = n ≡ m

  -- Give mutual recursive definitions for Even and Odd!
  mutual
    even : ℕ → Set
    even zero = ⊤
    even (suc n) = odd n

    odd : ℕ → Set
    odd zero = ⊥
    odd (suc n) = even n

  -- Define _>_ and _≥_ on top of _≤_!
  _>_ : ℕ → ℕ → Set
  a > b = (suc b) ≤ a

  _≥_ : ℕ → ℕ → Set
  a ≥ b = b ≤ a


  ¬ : Set → Set
  ¬ A = A → ⊥
