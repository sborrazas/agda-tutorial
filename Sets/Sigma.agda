module Sets.Sigma where

  open import Data.Bool using (Bool; true; false; if_then_else_)
  open import Data.Empty using (⊥)
  open import Data.Fin using (Fin; zero; suc)
  open import Data.List using (List; []; _∷_; _++_)
  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
  open import Data.Unit using (⊤; tt)
  open import Data.Product using (_×_; _,_)
  open import Function using (_$_; _∘_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
  open import Data.Empty using (⊥)

  data Σ (A : Set) (B : A → Set) : Set where
    _,_ : (a : A) → (b : B a) → Σ A B

  infixr 4 _,_

  Fin′ : ℕ → Set
  Fin′ n = Σ ℕ (λ x → x < n)

  toFin : ∀ {n} → Fin′ n → Fin n
  toFin (zero , (s≤s j)) = zero
  toFin ((suc a) , (s≤s j)) = suc (toFin (a , j))

  data _∈_ {A : Set}(x : A) : List A → Set where
    first : {xs : List A} → x ∈ x ∷ xs
    later : {y : A}{xs : List A} → x ∈ xs → x ∈ y ∷ xs

  infix 4 _∈_

  _!_ : ∀{A : Set} → List A → ℕ → Maybe A
  [] ! _           = nothing
  x ∷ xs ! zero    = just x
  x ∷ xs ! (suc n) = xs ! n

  infix 5 _!_

  -- Define lookup!
  lookup : ∀ {A}{x : A}(xs : List A) → x ∈ xs → Σ ℕ (λ n → xs ! n ≡ just x)
  lookup (x ∷ xs) first = (zero , refl)
  lookup (x ∷ xs) (later x∈xs) with (lookup xs x∈xs)
  ... | (pos , x∈xs2) = (suc pos , x∈xs2)

  fromList : List ⊤ → ℕ
  fromList [] = zero
  fromList (x ∷ xs) = suc (fromList xs)

  toList : ℕ → List ⊤
  toList zero = []
  toList (suc n) = tt ∷ toList n

  lemm : ∀ {a b : ℕ} → Data.Nat.suc a ≡ Data.Nat.suc b → a ≡ b
  lemm refl = refl

  from-injection : ∀ {a b} → fromList a ≡ fromList b → a ≡ b
  from-injection {[]}      {[]}      refl = refl
  from-injection {[]}      {x ∷ xs}  ()
  from-injection {x ∷ xs}  {[]}      ()
  from-injection {tt ∷ xs} {tt ∷ ys} p = cong (_∷_ tt) $ from-injection {xs} {ys} (lemm p)

  -- Define the following function:
  from-surjection : ∀ (n : ℕ) → Σ (List ⊤) ((_≡_ n) ∘ fromList)
  from-surjection zero = ([] , refl)
  from-surjection (suc n) with (from-surjection n)
  ... | (xs , a) = ((tt ∷ xs) , (cong suc a))
