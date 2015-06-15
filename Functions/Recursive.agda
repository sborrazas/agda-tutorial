module Functions.Recursive where

  open import Data.Bool using (Bool; true; false; not)
  open import Data.Nat using (ℕ; suc; zero)
  open import Sets.Recursive using (ℕ⁺; one; double; double+1; ℕ₂; zero; id; ℤ; z-zero; z-pos; z-neg)

  infixl 6 _+_
  _+_ : ℕ → ℕ → ℕ
  zero  + n = n
  suc m + n = suc (m + n)

  -- Define the following functions:

  pred  : ℕ → ℕ      -- predecessor (pred 0 = 0)
  pred 0 = 0
  pred (suc n) = n

  infixl 6 _∸_
  _∸_   : ℕ → ℕ → ℕ  -- subtraction (0 ∸ n = n)
  0 ∸ n = n
  n ∸ 0 = n
  (suc n) ∸ (suc m) = n ∸ m


  infixl 7 _*_
  _*_   : ℕ → ℕ → ℕ  -- multiplication
  0 * n = 0
  (suc n) * m = n + n * m

  infixl 6 _⊔_
  _⊔_   : ℕ → ℕ → ℕ  -- maximum
  0 ⊔ n = n
  n ⊔ 0 = n
  (suc n) ⊔ (suc m) = suc (n ⊔ m)

  infixl 7 _⊓_
  _⊓_   : ℕ → ℕ → ℕ  -- minimum
  0 ⊓ n = 0
  n ⊓ 0 = 0
  (suc n) ⊓ (suc m) = suc (n ⊓ m)

  ⌊_/2⌋ : ℕ → ℕ      -- half (⌊ 1 /2⌋ = 0)
  ⌊ 0 /2⌋ = 0
  ⌊ 1 /2⌋ = 0
  ⌊ (suc (suc n)) /2⌋ = suc ⌊ n /2⌋

  odd   : ℕ → Bool   -- is odd
  odd 0 = false
  odd 1 = true
  odd (suc (suc n)) = odd n

  even  : ℕ → Bool   -- is even
  even 0 = true
  even 1 = false
  even (suc (suc n)) = even n

  -- Define even and odd mutually with the mutual keyword!
  mutual
    odd`  : ℕ → Bool
    odd` 0 = false
    odd` (suc n) = not (even` n)

    even`  : ℕ → Bool
    even` 0 = true
    even` (suc n) = not (odd` n)

  _≡?_ : ℕ → ℕ → Bool -- is equal
  0 ≡? 0 = true
  (suc n) ≡? 0 = false
  0 ≡? (suc n) = false
  (suc n) ≡? (suc m) = n ≡? m

  _≤?_  : ℕ → ℕ → Bool  -- is less than or equal
  0 ≤? 0 = true
  0 ≤? (suc n) = true
  (suc n) ≤? 0 = false
  (suc n) ≤? (suc m) = n ≤? m

  -- Define the conversion function
  from : ℕ₂ → ℕ  -- hint: use _*_
  from zero = 0
  from (id one) = 1
  from (id (double n)) = 2 * (from (id n))
  from (id (double+1 n)) = suc (2 * (from (id n)))

  -- Define ℤ and some operations on it (_+_, _-_, _*_)!
  n++1 : ℕ⁺ → ℕ⁺
  n++1 one = double one
  n++1 (double x) = double+1 x
  n++1 (double+1 x) = double (n++1 x)

  -- _+z_ : ℤ → ℤ → ℤ
  -- z-zero +z x = x
  -- x +z z-zero = x
  -- (z-pos one) +z (z-pos y) with y -- 1 + y
  -- ... | one = z-pos (double one)
  -- ... | (double z) = z-pos (double+1 z)
  -- ... | (double+1 z) = {!!} -- (z-pos (double z)) +z (z-pos (double one))
  -- (z-pos one) +z (z-neg y) with y -- 1 - y
  -- ... | one = z-zero
  -- ... | (double z) = {!!}
  -- ... | (double+1 z) = z-neg {!!} -- 1 - (2 * z + 1) =
  -- (z-pos (double x)) +z (z-pos y) = {!!}
  -- (z-pos (double+1 x)) +z (z-pos y) = {!!}
  -- (z-pos (double x)) +z (z-neg y) = {!!}
  -- (z-pos (double+1 x)) +z (z-neg y) = {!!}
  -- (z-neg x) +z y = {!!}

  -- Define (recursive) mirroring of binary trees!
  data BinTree : Set where
    leaf : BinTree
    node : BinTree → BinTree → BinTree

  mirror : BinTree → BinTree
  mirror leaf = leaf
  mirror (node x y) = node (mirror y) (mirror x)
