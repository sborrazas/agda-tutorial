module Sets.Parametric where

  open import Data.Nat
  open import Sets.Enumerated

  infixr 5 _∷_
  data List (A : Set) : Set where
    []  :              List A
    _∷_ : A → List A → List A

  data PMaybe (A : Set) : Set where
    Just    : A → PMaybe A
    Nothing :     PMaybe A

  data PTree (A : Set) : Set where
    leaf : A → PTree A
    node : PTree A → PTree A → PTree A

  infixr 4 _,_
  infixr 2 _×_
  data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

  infixr 1 _⊎_
  data _⊎_ (A B : Set) : Set where
    inj₁ : A → A ⊎ B
    inj₂ : B → A ⊎ B

  -- Elements of (Bool ⊎ Top)
  a : Bool ⊎ ⊤ → ⊤
  a (inj₁ true) = tt
  a (inj₁ false) = tt
  a (inj₂ tt) = tt

  -- Elements of ((Top ⊎ Top) ⊎ Top)
  b : ⊤ ⊎ (⊤ ⊎ ⊤) → ⊤
  b (inj₁ tt) = tt
  b (inj₂ (inj₁ tt)) = tt
  b (inj₂ (inj₂ tt)) = tt

  data MaybeU (A : Set) : Set where
    mu : A ⊎ ⊤ -> MaybeU A


  data List₁ (A B : Set) : Set
  data List₂ (A B : Set) : Set

  data List₁ (A B : Set) where
    []  :                 List₁ A B
    _∷_ : A → List₂ A B → List₁ A B

  data List₂ (A B : Set) where
    _∷_ : B → List₁ A B → List₂ A B

  -- Smallest 5 elements of List₁ ⊤ Bool
  -- []
  -- tt ∷ (false ∷ [])
  -- tt ∷ (true ∷ [])
  -- tt ∷ (false ∷ tt ∷ (false ∷ []))
  -- tt ∷ (false ∷ tt ∷ (true ∷ []))

  data AlterList (A B : Set) : Set  where
    []  :                     AlterList A B
    _∷_ : A → AlterList B A → AlterList A B

  -- List the first smallest 4 (+4) elements of the following dataset
  -- (let A = ⊤ and B = Bool and reversed):
  -- []
  -- tt ∷ []
  -- tt ∷ (false ∷ [])
  -- tt ∷ (true ∷ [])
  -- tt ∷ (false ∷ tt ∷ (false ∷ []))
  --
  -- c : AlterList ⊤ Bool
  -- c = tt ∷ (false ∷ tt ∷ (false ∷ []))

  data T4 (A : Set) : Set where
    quad : A → A → A → A → T4 A

  data Square (A : Set) : Set where
    zero :            A  → Square A   -- 2^0 rows
    suc  : Square (T4 A) → Square A   -- 2^(n+1) rows
