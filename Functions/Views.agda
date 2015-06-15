module Functions.Views where

  open import Data.Nat using (ℕ; zero; suc; _<_; _>_; s≤s; z≤n; _+_; _*_)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
  open import Function using (_∘_)

  data Even : ℕ → Set
  data Odd  : ℕ → Set

  data Even where
    zero : Even zero
    odd  : ∀ {n} → Odd n → Even (suc n)

  data Odd where
    even : ∀ {n} → Even n → Odd (suc n)

  parity : ∀ n → Even n ⊎ Odd n
  parity zero = inj₁ zero
  parity (suc n) with parity n
  parity (suc n) | inj₁ x = inj₂ (even x)
  parity (suc n) | inj₂ y = inj₁ (odd y)

  -- The ordering view is a view on ℕ × ℕ (in curried form):
  -- Define the ordering view!
  ordering : ∀ n m → (n < m) ⊎ ((n ≡ m) ⊎ (n > m))
  ordering zero zero = inj₂ (inj₁ refl)
  ordering zero (suc n) = inj₁ (s≤s z≤n)
  ordering (suc n) zero = inj₂ (inj₂ (s≤s z≤n))
  ordering (suc m) (suc n) with (ordering m n)
  ... | inj₁ s<s = inj₁ (s≤s s<s)
  ... | inj₂ (inj₁ s=s) = inj₂ (inj₁ (cong suc s=s))
  ... | inj₂ (inj₂ s>s) = inj₂ (inj₂ (s≤s s>s))

  data Parity : ℕ → Set where
    even : ∀ n → Parity (n * 2)
    odd  : ∀ n → Parity (1 + n * 2)

  data Ordering : ℕ → ℕ → Set where
    less    : ∀ m k → Ordering m (suc (m + k))
    equal   : ∀ m   → Ordering m m
    greater : ∀ m k → Ordering (suc (m + k)) m

  -- Define the functions
  parity′ : ∀ n → Parity n
  parity′ zero = even zero
  parity′ (suc n) with (parity′ n)
  parity′ (suc .(m * 2)) | even m = odd m
  parity′ (suc .(1 + (m * 2))) | odd m = even (suc m)

  compare : ∀ m n → Ordering m n
  compare zero zero = equal zero
  compare zero (suc n) = less zero n
  compare (suc n) zero = greater zero n
  compare (suc m) (suc n) with (compare m n)
  compare (suc .a) (suc .(suc (a + b))) | less a b = less (suc a) b
  compare (suc .a) (suc .a) | equal a = equal (suc a)
  compare (suc .(suc (b + a))) (suc .b) | greater b a = greater (suc b) a

  -- Define division by 2 with the help of Parity:
  ⌊_/2⌋ : ℕ → ℕ      -- half (⌊ 1 /2⌋ = 0)
  ⌊ n /2⌋ with (parity′ n)
  ⌊ .(m * 2) /2⌋ | even m = m
  ⌊ .(1 + m * 2) /2⌋ | odd m = m

  -- Define congruence classes of 4 as a view on natural numbers!
  -- Hint: use Parity when implementing the view function.
  data Congruence4 : ℕ → Set where
    c40 : ∀ n → Congruence4 (n * 4)
    c41 : ∀ n → Congruence4 (1 + n * 4)
    c42 : ∀ n → Congruence4 (2 + n * 4)
    c43 : ∀ n → Congruence4 (3 + n * 4)

  lem-times-4 : ∀ p → (p * 2) * 2 ≡ p * 4
  lem-times-4 zero = refl
  lem-times-4 (suc n) = cong (suc ∘ suc ∘ suc ∘ suc) (lem-times-4 n)

  congruence4 : ∀ n → Congruence4 n
  congruence4 n with parity′ n
  congruence4 .(m * 2) | even m with m | (parity′ m)
  congruence4 .(m * 2) | even m | .(p * 2) | even p with ((p * 2) * 2) | (lem-times-4 p)
  congruence4 .(m * 2) | even m | .(p * 2) | even p | .(p * 4) | refl = c40 p
  congruence4 .(m * 2) | even m | .(1 + p * 2) | odd p with ((p * 2) * 2) | (lem-times-4 p)
  congruence4 .(m * 2) | even m | .(1 + p * 2) | odd p | .(p * 4) | refl = c42 p
  congruence4 .(1 + m * 2) | odd m with m | (parity′ m)
  congruence4 .(1 + m * 2) | odd m | .(p * 2) | even p with ((p * 2) * 2) | (lem-times-4 p)
  congruence4 .(1 + m * 2) | odd m | .(p * 2) | even p | .(p * 4) | refl = c41 p
  congruence4 .(1 + m * 2) | odd m | .(1 + p * 2) | odd p with ((p * 2) * 2) | (lem-times-4 p)
  congruence4 .(1 + m * 2) | odd m | .(1 + p * 2) | odd p | .(p * 4) | refl = c43 p
