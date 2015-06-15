module Functions.Views.Decidability where

  open import Data.Nat   using (ℕ; zero; suc; pred; _+_; _≤_; s≤s; z≤n; _<_; _>_)
  open import Data.Bool  using (Bool; true; false; if_then_else_; not)
  open import Data.Unit  using (⊤; tt)
  open import Data.Empty using (⊥)
  open import Function   using (const; _$_; _∘_)
  open import Relation.Nullary using (¬_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)

  data Dec (A : Set) : Set where
    yes :   A → Dec A
    no  : ¬ A → Dec A

  -- Define the decidability view for 1 < 2, 1 ≡ 1, 1 ≡ 2 and 1 > 2:
  1<2 : Dec (1 < 2)
  1<2 = yes (s≤s (s≤s z≤n))

  1≡1 : Dec (1 ≡ 1)
  1≡1 = yes refl

  1≡2-bot : (1 ≡ 2) → ⊥
  1≡2-bot ()

  1≡2 : Dec (1 ≡ 2)
  1≡2 = no 1≡2-bot

  1>2-bot : (1 > 2) → ⊥
  1>2-bot (s≤s ())

  1>2 : Dec (1 > 2)
  1>2 = no 1>2-bot

  -- Define the decidability view for n ≡ m and n ≤ m where n m : ℕ:
  suc<>zero : ∀ n → ¬ suc n ≡ zero
  suc<>zero zero ()
  suc<>zero (suc n) ()

  zero<>suc : ∀ n → ¬ zero ≡ suc n
  zero<>suc zero ()
  zero<>suc (suc n) ()

  _≟_ : (a b : ℕ) → Dec (a ≡ b)
  zero ≟ zero = yes refl
  (suc n) ≟ zero = no (suc<>zero n)
  zero ≟ (suc n) = no (zero<>suc n)
  (suc m) ≟ (suc n) with (m ≟ n)
  ... | yes m=n = yes (cong suc m=n)
  ... | no m<>n = no (m<>n ∘ cong pred)

  suc>zero : ∀ n → ¬ suc n ≤ zero
  suc>zero zero ()
  suc>zero (suc n) ()

  cong-pred≤ : ∀ {m n} → suc m ≤ suc n → m ≤ n
  cong-pred≤ (s≤s m≤n) = m≤n

  _≤?_ : (a b : ℕ) → Dec (a ≤ b)
  zero ≤? zero = yes z≤n
  zero ≤? (suc n) = yes z≤n
  (suc n) ≤? zero = no (suc>zero n)
  (suc m) ≤? (suc n) with m ≤? n
  ... | yes m≤n = yes (s≤s m≤n)
  ... | no m≤n = no (m≤n ∘ cong-pred≤)

  ⌊_⌋ : {P : Set} → Dec P → Bool
  ⌊ yes _ ⌋ = true
  ⌊ no  _ ⌋ = false
