module Sets.Parameters_vs_Indices where

  open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
  open import Data.List using (List; []; _∷_)
  open import Sets.Enumerated using (⊤; ⊥; tt)

  infix 4 _≡_
  data  _≡_ {A : Set} (x : A) : A → Set  where
    refl : x ≡ x

  infix 4 _∈_
  data _∈_ {A : Set}(x : A) : List A → Set where
    first : ∀ {xs} → x ∈ x ∷ xs
    later : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

  -- Define _⊆_ {A : Set} : List A → List A → Set!
  data _⊆_ {A : Set} : List A → List A → Set where
    c-empty : [] ⊆ []
    c-drop  : ∀ {x xs ys} → xs ⊆ ys → xs ⊆ (x ∷ ys)
    c-take  : ∀ {x xs ys} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)

  -- Prove that 1 ∷ 2 ∷ [] ⊆ 1 ∷ 2 ∷ 3 ∷ [] is non-empty!
  1-2⊆1-2-3 : (1 ∷ 2 ∷ []) ⊆ (1 ∷ 2 ∷ 3 ∷ [])
  1-2⊆1-2-3 = c-take (c-take (c-drop c-empty))

  -- Prove that 1 ∷ 2 ∷ 3 ∷ [] ⊆ 1 ∷ 2 ∷ [] is empty!
  1-2-3⊆1-2 : (1 ∷ 2 ∷ 3 ∷ []) ⊆ (1 ∷ 2 ∷ []) → ⊥
  1-2-3⊆1-2 (c-take (c-take ()))
  1-2-3⊆1-2 (c-drop (c-drop ()))
  1-2-3⊆1-2 (c-take (c-drop ()))

  -- Define a permutation predicate!
  data Perm {A : Set} : List A → List A → Set where
    p-empty :                                          Perm [] []
    p-head  : ∀ {x xs ys} → Perm xs ys →               Perm (x ∷ xs) (x ∷ ys)
    p-swap  : ∀ {x x' xs ys} → Perm (x ∷ x' ∷ xs) ys → Perm (x' ∷ x ∷ xs) ys
    p-trans : ∀ {xs ys zs} → Perm xs ys → Perm ys zs → Perm xs zs

  1-2-3perm2-3-1 : Perm (1 ∷ 2 ∷ 3 ∷ []) (2 ∷ 3 ∷ 1 ∷ [])
  1-2-3perm2-3-1 = p-swap (p-head (p-swap (p-head (p-head p-empty))))

  1-2-3perm3-2-1 : Perm (1 ∷ 2 ∷ 3 ∷ []) (3 ∷ 2 ∷ 1 ∷ [])
  1-2-3perm3-2-1 = p-trans (p-head (p-swap (p-head (p-head p-empty)))) (p-swap (p-head (p-swap (p-head (p-head p-empty)))))

  -- Define a sort predicate!
  data Sort : List ℕ → List ℕ → Set where
    s-empty :                                          Sort [] []
