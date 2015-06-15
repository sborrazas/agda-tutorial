module Sets.Propositions where

  open import Data.Nat using (ℕ; zero; suc)
  open import Sets.Enumerated using (⊤; ⊥; tt)
  open import Sets.Parametric using (_×_; _,_; _⊎_; inj₁; inj₂)
  open import Sets.Recursive using (ℕ⁺; one; double; double+1)


  -- Construct one proof for each proposition if possible:
  ⊤×⊤ : ⊤ × ⊤
  ⊤×⊤ = tt , tt

  -- ⊤×⊥ : ⊤ × ⊥
  -- ⊥×⊥ : ⊥ × ⊥

  ⊤⊎⊤ : ⊤ ⊎ ⊤
  ⊤⊎⊤ = inj₁ tt

  ⊤⊎⊥ : ⊤ ⊎ ⊥
  ⊤⊎⊥ = inj₁ tt

  -- ⊥⊎⊥ : ⊥ ⊎ ⊥

  combined : ⊥ ⊎ ⊤ ⊎ ⊤ × (⊥ ⊎ ⊥) ⊎ ⊤
  combined = inj₂ (inj₁ tt)

  infix 4 _≤_
  data  _≤_ : ℕ → ℕ → Set where
    z≤n : {n : ℕ}   →         zero  ≤ n
    s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

  infix 4 _≤′_
  data _≤′_ : ℕ → ℕ → Set where
    ≤′-refl : {m : ℕ} →                       m ≤′ m
    ≤′-step : {m : ℕ} → {n : ℕ} →  m ≤′ n  →  m ≤′ suc n

  0≤1 : 1 ≤ 10
  0≤1 = s≤s z≤n

  -- Prove that 3 ≤ 7!
  3≤7 : 3 ≤ 7
  3≤7 = s≤s (s≤s (s≤s z≤n))

  7≰3 : 7 ≤ 3 → ⊥
  7≰3 (s≤s (s≤s (s≤s ())))

  -- Prove that 4 ≤ 2 is empty!
  4≰2 : 4 ≤ 2 → ⊥
  4≰2 (s≤s (s≤s ()))

  8≰4 : 8 ≤ 4 → ⊥
  8≰4 (s≤s x) = 7≰3 x

  -- Define an indexed set _isDoubleOf_ : ℕ → ℕ → Set such that m isDoubleOf n
  -- is non-empty iff m is the double of n!
  data _isDoubleOf_ : ℕ → ℕ → Set where
    zero-double : 0 isDoubleOf 0
    suc-double  : ∀ {n m} → (n isDoubleOf m) → (suc (suc n)) isDoubleOf (suc m)

  -- Prove that 8 isDoubleOf 4 is non-empty!
  8isDoubleOf4 : 8 isDoubleOf 4
  8isDoubleOf4 = suc-double (suc-double (suc-double (suc-double zero-double)))

  -- Prove that 9 isDoubleOf 4 is empty!
  9isDoubleOf4 : 9 isDoubleOf 4 → ⊥
  9isDoubleOf4 (suc-double (suc-double (suc-double (suc-double ()))))

  -- Define an indexed set Odd : ℕ → Set such that odd n is non-empty iff n is
  -- odd!
  data Odd : ℕ → Set where
    one-odd : Odd (suc 0)
    suc-odd : ∀ {n} → Odd n → Odd (suc (suc n))

  -- Prove that Odd 9 is non-empty!
  Odd9 : Odd 9
  Odd9 = suc-odd (suc-odd (suc-odd (suc-odd one-odd)))

  -- Prove that Odd 8 is empty!
  Odd8 : Odd 8 → ⊥
  Odd8 (suc-odd (suc-odd (suc-odd (suc-odd ()))))

  -- Define Even : ℕ → Set and Odd : ℕ → Set mutually!
  data Even` : ℕ → Set
  data Odd`  : ℕ → Set

  data Even` where
    zero-even : Even` zero
    suc-even  : ∀ {n} → Odd` n → Even` (suc n)

  data Odd` where
    suc-odd : ∀ {n} → Even` n → Odd` (suc n)

  -- Define equality _≡_ : ℕ → ℕ → Set!
  data _≡_ : ℕ → ℕ → Set where
    zero-eq : 0 ≡ 0
    suc-eq  : ∀ {n} → (suc n) ≡ (suc n)

  -- Define non-equality _≠_ : ℕ → ℕ → Set!
  data _≠_ : ℕ → ℕ → Set where
    zero-eq : ∀ {n} → 0 ≠ (suc n)
    one-eq  : ∀ {n} → (suc n) ≠ 0
    suc-eq  : ∀ {n m} → n ≠ m → (suc n) ≠ (suc m)

  data _+_≡_ : ℕ → ℕ → ℕ → Set where
    znn : ∀ {n} → 0 + n ≡ n
    sns : ∀ {m n k} → m + n ≡ k → suc m + n ≡ suc k

  -- Prove that 5 + 5 = 10!
  5+5≡10 : 5 + 5 ≡ 10
  5+5≡10 = sns (sns (sns (sns (sns znn))))

  -- Prove that 2 + 2 ≠ 5!
  2+2≠5 : 2 + 2 ≡ 5 → ⊥
  2+2≠5 (sns (sns ()))

  -- Define _⊓_ : ℕ → ℕ → Set such that n ⊓ m ≡ k iff k is the minimum of n and
  -- m!
  data _⊓_≡_ : ℕ → ℕ → ℕ → Set where
    min-rzero : ∀ {n}   → n ⊓ 0 ≡ 0
    min-lzero : ∀ {n}   → 0 ⊓ n ≡ 0
    min-left  : ∀ {n m} → n ⊓ m ≡ n → (suc n) ⊓ (suc m) ≡ (suc n)
    min-right : ∀ {n m} → n ⊓ m ≡ m → (suc n) ⊓ (suc m) ≡ (suc m)

  -- Prove that 3 ⊓ 5 ≡ 3 is non-empty!
  3⊓5≡3 : 3 ⊓ 5 ≡ 3
  3⊓5≡3 = min-left (min-left (min-left min-lzero))

  -- Prove that 3 ⊓ 5 ≡ 5 is empty!
  3⊓5≡5 : 3 ⊓ 5 ≡ 5 → ⊥
  3⊓5≡5 (min-right (min-right (min-right ())))

  -- Define _⊔_ : ℕ → ℕ → Set such that n ⊔ m ≡ k iff k is the maximum of n and
  -- m!
  data _⊔_≡_ : ℕ → ℕ → ℕ → Set where
    max-rzero : ∀ {n}   → n ⊔ 0 ≡ n
    max-lzero : ∀ {n}   → 0 ⊔ n ≡ n
    max-left  : ∀ {n m} → n ⊔ m ≡ n → (suc n) ⊔ (suc m) ≡ (suc n)
    max-right : ∀ {n m} → n ⊔ m ≡ m → (suc n) ⊔ (suc m) ≡ (suc m)

  -- Prove that 3 ⊔ 5 ≡ 5 is non-empty!
  3⊔5≡5 : 3 ⊔ 5 ≡ 5
  3⊔5≡5 = max-right (max-right (max-right max-lzero))

  -- Prove that 3 ⊔ 5 ≡ 3 is empty!
  3⊔5≡3 : 3 ⊔ 5 ≡ 3 → ⊥
  3⊔5≡3 (max-left (max-left (max-left ())))

  data _≤″_ : ℕ → ℕ → Set where
    ≤+ : ∀ {m n k} → m + n ≡ k → m ≤″ k

  -- Define _isDoubleOf2_ : ℕ → ℕ → Set on top of _+_≡_!
  data _isDoubleOf2_ : ℕ → ℕ → Set where
    zero-double` : 0 isDoubleOf2 0
    suc-double`  : ∀ {n k} → n + n ≡ k → k isDoubleOf2 n

  -- data _+_≡_ : ℕ → ℕ → ℕ → Set where
  --   znn : ∀ {n} → zero + n ≡ n
  --   sns : ∀ {m n k} → m + n ≡ k → suc m + n ≡ suc k

  -- Prove that 8 isDoubleOf2 4 is non-empty!
  8isDoubleOf24 : 8 isDoubleOf2 4
  8isDoubleOf24 = suc-double` (sns (sns (sns (sns znn))))

  -- Prove that 9 isDoubleOf2 4 is empty!
  9isDoubleOf24 : (9 isDoubleOf2 4) → ⊥
  9isDoubleOf24 (suc-double` (sns (sns (sns (sns ())))))

  -- Define _*_≡_ : ℕ → ℕ → Set with the help of _+_≡_!
  data _*_≡_ : ℕ → ℕ → ℕ → Set where
    mul-zero : ∀ {n} → 0 * n ≡ 0
    mul-suc  : ∀ {n m k j} → n * m ≡ k → k + m ≡ j → (suc n) * m ≡ j

  5+3≡8 : 5 + 3 ≡ 8
  5+3≡8 = sns (sns (sns (sns (sns znn))))

  2+3≡5 : 2 + 3 ≡ 5
  2+3≡5 = sns (sns znn)

  1+1≡2 : 1 + 1 ≡ 2
  1+1≡2 = sns znn

  6+3≡9 : 6 + 3 ≡ 9
  6+3≡9 = sns 5+3≡8

  3+3≡6 : 3 + 3 ≡ 6
  3+3≡6 = sns 2+3≡5

  0+3≡3 : 0 + 3 ≡ 3
  0+3≡3 = znn

  -- Prove that 3 * 3 ≡ 9 is non-empty!
  3*3≡9 : 3 * 3 ≡ 9
  3*3≡9 = mul-suc (mul-suc (mul-suc mul-zero 0+3≡3) 3+3≡6) 6+3≡9

  0+3≡2 : 0 + 3 ≡ 2 → ⊥
  0+3≡2 ()

  -- Prove that 3 * 3 ≡ 8 is empty!
  3*3≡8 : 3 * 3 ≡ 8 → ⊥
  -- 3 * 3 ≡ 8 mul-suc (2 * 3 ≡ 5) (5 + 3 ≡ 8)
  -- 2 * 3 ≡ 5 mul-suc (1 * 3 ≡ 2) (2 + 3 ≡ 5)
  -- 1 * 3 ≡ 2 mul-suc (0 * 3 ≡ ?) (? + 3 ≡ 2)
  -- 1 * 3 ≡ 2 mul-suc (0 * 3 ≡ 0) (0 + 3 ≡ 2)

  -- 3*3≡8 (mul-suc (mul-suc (mul-suc (mul-zero) znn) 2+3≡5) 5+3≡8) = {!!}
  3*3≡8 (mul-suc (mul-suc (mul-suc mul-zero znn) (sns (sns (sns znn)))) (sns (sns (sns (sns (sns (sns ())))))))

  -- Define _≈_ : ℕ → ℕ⁺ → Set which represents the (canonical) isomorphism between ℕ and ℕ⁺!
  data _≈_ : ℕ → ℕ⁺ → Set where
    xone      : (suc zero) ≈ one
    xdouble   : ∀ {n n+ m} → n ≈ n+ → n + n ≡ m → m ≈ (double n+)
    xdouble+1 : ∀ {n n+} → n ≈ (double n+) → (suc n) ≈ (double+1 n+)

  2+2≡4 : 2 + 2 ≡ 4
  2+2≡4 = sns (sns znn)

  -- Prove that 5 ≈ double+1 (double one) is non-empty!
  5≈d1d : 5 ≈ double+1 (double one)
  5≈d1d = xdouble+1 (xdouble (xdouble xone 1+1≡2) 2+2≡4)

  -- Prove that 4 ≈ double+1 (double one) is empty!
  4≈d1d : 4 ≈ double+1 (double one) → ⊥
  4≈d1d (xdouble+1 (xdouble (xdouble xone 1+1≡2) (sns (sns (sns ())))))
