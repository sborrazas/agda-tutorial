module Functions.Polymorphic where

  open import Data.Nat
  open import Data.Unit using (⊤; tt)
  open import Sets.Parametric using (List; []; _∷_; _,_; _×_; _⊎_; inj₁; inj₂)
  open import Sets.Parameters_vs_Indices using (_≡_; refl)

  infixr 5 _++_
  _++_ : {A : Set} → List A → List A → List A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  -- Define two functions which define the isomorphism between List ⊤ and ℕ!

  fromList : List ⊤ → ℕ
  fromList [] = zero
  fromList (tt ∷ xs) = suc (fromList xs)

  toList : ℕ → List ⊤
  toList zero = []
  toList (suc n) = tt ∷ (toList n)

  -- infixl 6 _+_
  -- _+_ : ℕ → ℕ → ℕ
  -- zero  + n = n
  -- suc m + n = suc (m + n)

  lem-fromList : {A : Set}(a : List ⊤)(b : List ⊤) → (fromList (a ++ b)) ≡ (fromList a + fromList b)
  lem-fromList [] _ = refl
  lem-fromList (tt ∷ xs) ys = {!!}

  -- lem-fromList (tt ∷ xs) ys with ((suc (fromList xs)) + (fromList ys)) | (lem-fromList xs ys)
  -- ... | (suc a) | refl = refl

  -- Define the following functions on lists:
  map  : {A B : Set} → (A → B)      → List A → List B -- regular map
  map f [] = []
  map f (x ∷ xs) = (f x) ∷ (map f xs)

  maps : {A B : Set} → List (A → B) → List A → List B -- pairwise map
  maps [] _ = []
  maps (f ∷ fs) [] = []
  maps (f ∷ fs) (x ∷ xs) = (f x) ∷ (maps fs xs)

  -- Define the singleton list function
  [_] : {A : Set} → A → List A
  [ x ] = x ∷ []

  id : {A : Set} → A → A
  id a = a

  -- Define const : {A B : Set} → A → B → A!
  const : {A B : Set} → A → B → A
  const x _ = x

  -- Define flip : {A B C : Set} → (A → B → C) → B → A → C!
  flip : {A B C : Set} → (A → B → C) → B → A → C
  flip f b a = f a b

  -- Define a function which swaps the two elements of the cartesian product!
  swap : {A B : Set} → A × B → B × A
  swap (a , b) = (b , a)

  -- Define the following functions:
  proj₁ : {A B : Set} → A × B → A
  proj₁ (a , b) = a

  -- Define a function which swaps the two elements of the disjoint union!
  swapdu : {A B : Set} → A ⊎ B → B ⊎ A
  swapdu (inj₁ a) = inj₂ a
  swapdu (inj₂ b) = inj₁ b

  -- Define the eliminator function for disjoint union:
  [_,_] : {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
  [ fa , fb ] (inj₁ a) = fa a
  [ fa , fb ] (inj₂ b) = fb b
