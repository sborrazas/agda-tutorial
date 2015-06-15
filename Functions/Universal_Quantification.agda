module Functions.Universal_Quantification where

  open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _≤′_; ≤′-step; ≤′-refl)
  open import Data.Fin using (Fin; zero; suc; toℕ)
  open import Data.Empty using (⊥)
  open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
  open import Function using (flip; _$_; _∘_)

  -- ≤-refl : (n : ℕ) → n ≤ n
  -- ≤-refl zero    = z≤n
  -- ≤-refl (suc n) = s≤s (≤-refl n)

  ≤-refl : {n : ℕ} → n ≤ n
  ≤-refl {zero}    = z≤n
  ≤-refl {suc n} = s≤s (≤-refl {n})

  -- Define the following functions (prove these properties):
  ≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
  ≤-trans z≤n _ = z≤n
  ≤-trans (s≤s x) (s≤s y) = s≤s (≤-trans x y)

  total : ∀ m n → m ≤ n ⊎ n ≤ m -- hint: use [_,_]′
  total zero _ = inj₁ z≤n
  total _ zero = inj₂ z≤n
  total (suc x) (suc y) = ([ (inj₁ ∘ s≤s) , (inj₂ ∘ s≤s) ]′) (total x y)

  -- From the 4 above properties follows that _≤_ is a total order on ℕ.
  -- (We can look at _≤_ as a relation over ℕ.)
  ≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
  ≤-pred (s≤s z≤n) = z≤n
  ≤-pred (s≤s (s≤s n)) = s≤s (≤-pred (s≤s n))

  ≤-mono : ∀ {m n k} → n ≤ m → k + n ≤ k + m
  ≤-mono {k = zero} n≦m = n≦m
  ≤-mono {k = (suc x)} n≦m = s≤s (≤-mono {k = x} n≦m)

  -- Define the following functions:
  ≤-step : ∀ {m n} → m ≤ n → m ≤ 1 + n
  ≤-step z≤n = z≤n
  ≤-step (s≤s n) = s≤s (≤-step n)

  ≤′⇒≤ : ∀ {a b} → a ≤′ b → a ≤ b
  ≤′⇒≤ ≤′-refl = ≤-refl
  ≤′⇒≤ (≤′-step a≤′b) = ≤-step (≤′⇒≤ a≤′b)

  z≤′n : ∀ {n} → zero ≤′ n
  z≤′n {zero} = ≤′-refl
  z≤′n {suc n} = ≤′-step (z≤′n {n})

  s≤′s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
  s≤′s ≤′-refl = ≤′-refl
  s≤′s (≤′-step m≤′n) = ≤′-step (s≤′s m≤′n)

  ≤⇒≤′ : ∀ {a b} → a ≤ b → a ≤′ b
  ≤⇒≤′ z≤n = z≤′n
  ≤⇒≤′ (s≤s x) = s≤′s (≤⇒≤′ x)

  -- Define fin≤:
  fin≤ : ∀ {n}(m : Fin n) → toℕ m < n
  fin≤ zero = s≤s z≤n
  fin≤ (suc x) = s≤s (fin≤ x)
