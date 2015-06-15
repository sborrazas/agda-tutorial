module Sets.Recursive where

  open import Sets.Enumerated using (Bool; true; false)

  data ℕ : Set where
    zero :     ℕ
    suc  : ℕ → ℕ

  data ℕ⁺ : Set where
    one      :      ℕ⁺
    double   : ℕ⁺ → ℕ⁺
    double+1 : ℕ⁺ → ℕ⁺

  data ℕ₂ : Set where
    zero :      ℕ₂
    id   : ℕ⁺ → ℕ₂

  data ℤ : Set where
    z-zero : ℤ
    z-pos  : ℕ⁺ → ℤ
    z-neg  : ℕ⁺ → ℤ

  data BinTree : Set where
    leaf : BinTree
    node : BinTree → BinTree → BinTree

  bin₁ : BinTree
  bin₁ = leaf

  bin₂ : BinTree
  bin₂ = node leaf leaf

  bin₃ : BinTree
  bin₃ = node (node leaf leaf) (node leaf leaf)

  bin₄ : BinTree
  bin₄ = node (node (node leaf leaf) leaf) leaf

  data BinNTree : Set where
    n-leaf : ℕ → BinNTree
    n-node :     BinNTree

  data BinN2Tree : Set where
    n2-leaf :     BinN2Tree
    n2-node : ℕ → BinN2Tree

  data BinNBoolTree : Set where
    nbool-leaf : Bool → BinNBoolTree
    nbool-node : ℕ    → BinNBoolTree

  data NList : Set where
    n-nil  : NList
    n-cons : ℕ → NList → NList

  data N+List : Set where
    n+-base : ℕ → N+List
    n+-cons : ℕ → N+List → N+List
