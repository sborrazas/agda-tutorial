module Sets.Indexed where

  open import Data.Empty    using (⊥)
  open import Data.Unit     using (⊤; tt)
  open import Data.Sum      using (_⊎_; inj₁; inj₂)
  open import Data.Bool     using (Bool; true; false)
  open import Data.Nat      using (ℕ; zero; suc)

  data Fin : ℕ → Set where
    zero : (n : ℕ) → Fin (suc n)
    suc  : (n : ℕ) → Fin n → Fin (suc n)

  a11 : Fin 1
  a11 = zero 0

  a21 : Fin 2
  a21 = zero 1

  a22 : Fin 2
  a22 = suc 1 a11

  a31 : Fin 3
  a31 = zero 2

  a32 : Fin 3
  a32 = suc 2 a21

  a33 : Fin 3
  a33 = suc 2 a21


  -- Define a Bool indexed family of sets such that the set indexed by false
  -- contains no elements and the set indexed by true contains one element!
  data FinBool : Bool → Set where
    ft : ⊤ → FinBool true
    ff : ⊥ → FinBool false

  -- Define a ℕ indexed family of sets such that the sets indexed by even
  -- numbers contain one element and the others are empty!
  data FinEven : ℕ → Set where
    zero : ⊤       → FinEven zero
    suc  : (n : ℕ) → FinEven (suc (suc n))


  data Vec (A : Set) : ℕ → Set where
    []   :                         Vec A zero
    cons : (n : ℕ) → A → Vec A n → Vec A (suc n)

  -- Define a Bool indexed family of sets with two parameters, A and B, such
  -- that the set indexed by false contains an A element and the set indexed by
  -- true contains a B element!

  data EitherBool(A B : Set) : Bool → Set where
    right : A → EitherBool A B false
    left  : B → EitherBool A B true
