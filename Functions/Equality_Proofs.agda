module Functions.Equality_Proofs where

  open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
  open import Data.List using (List; []; _∷_; _++_)
  open import Data.Unit using (⊤; tt)
  open import Data.Product using (_×_; _,_)
  open import Function using (_$_)

  infix 4 _≡_
  data _≡_ {A : Set} (x : A) : A → Set  where
    refl : x ≡ x

  refl'  : ∀ {A} (a : A) → a ≡ a
  refl' a = refl

  sym   : ∀ {A} {a b : A} → a ≡ b → b ≡ a
  sym refl = refl   -- after pattern matching on 'refl', 'a' and 'b' coincides

  trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  trans refl refl = refl

  -- Prove that every function is compatible with the equivalence relation (congruency):
  cong : ∀ {A B} {m n : A} → (f : A → B) → m ≡ n → f m ≡ f n
  cong f refl = refl

  1+1≡2 : 1 + 1 ≡ 2
  1+1≡2 = refl

  +-right-identity : ∀ n → n + 0 ≡ n
  +-right-identity zero    = refl
  +-right-identity (suc n) = cong suc (+-right-identity n)

  -- Finish the ingredients of the proof that (ℕ, _+_) is a commutative monoid!
  +-left-identity : ∀ a → 0 + a ≡ a
  +-left-identity a = refl

  +-assoc : ∀ a b c → a + (b + c) ≡ (a + b) + c -- hint: use cong
  +-assoc zero b c = refl
  +-assoc (suc a) b c = cong suc (+-assoc a b c)

  -- For commutativity you need a helper function first:
  m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
  m+1+n≡1+m+n zero n = refl
  m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

  fromList : List ⊤ → ℕ
  fromList [] = zero
  fromList (x ∷ xs) = suc (fromList xs)

  toList : ℕ → List ⊤
  toList zero = []
  toList (suc n) = tt ∷ toList n

  -- Let's prove that fromList and toList are inverses of each other and that
  -- they preserve the operations _++_ and _+_!
  from-to : ∀ a → fromList (toList a) ≡ a
  from-to zero = refl
  from-to (suc n) = cong suc (from-to n)

  to-from : ∀ a → toList (fromList a) ≡ a
  to-from [] = refl
  to-from (tt ∷ xs) = cong (_∷_ tt) (to-from xs)

  fromPreserves++ : ∀ (a b : List ⊤) → fromList (a ++ b) ≡ fromList a + fromList b
  fromPreserves++ [] b = refl
  fromPreserves++ (tt ∷ xs) b = cong suc (fromPreserves++ xs b)

  toPreserves+ : ∀ (a b : ℕ) → toList (a + b) ≡ toList a ++ toList b
  toPreserves+ zero b = refl
  toPreserves+ (suc n) b = cong (_∷_ tt) (toPreserves+ n b)

  infixr 2 _≡⟨_⟩_
  _≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡>⟨ refl ⟩ refl = refl

  infix  2 _∎
  _∎ : ∀ {A : Set} (x : A) → x ≡ x
  x ∎ = refl

  +-comm' : (n m : ℕ) → n + m ≡ m + n
  +-comm' zero    n = sym (+-right-identity n)
  +-comm' (suc m) n =
        suc m + n
      ≡⟨ refl ⟩
        suc (m + n)
      ≡⟨ cong suc (+-comm' m n) ⟩
        suc (n + m)
      ≡⟨ sym (m+1+n≡1+m+n n m) ⟩
        n + suc m
      ∎

  -- helper functions:
  n*0≡0 : ∀ n → n * 0 ≡ 0
  n*0≡0 zero = refl
  n*0≡0 (suc n) = n*0≡0 n

  -- m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
  -- +-assoc : ∀ a b c → a + (b + c) ≡ (a + b) + c -- hint: use cong
  coso : ∀ {a b c} → suc (((suc a) * b) + c) ≡ suc ((b + a * b) + c)
  -- coso {a} {b} {c} = cong (λ x → suc (x + c)) refl
  coso {a} {b} {c} = cong {ℕ} {ℕ} {(suc a * b)} {(b + a * b)} (λ x → suc (x + c)) refl

  *-suc : ∀ n m → n + n * m ≡ n * suc m
  *-suc zero _ = refl
  *-suc (suc n) m =
      (suc n + suc n * m)
    ≡⟨ +-comm' (suc n) (suc n * m) ⟩
      (suc n * m) + suc n
    ≡⟨ m+1+n≡1+m+n (suc n * m) n ⟩
      suc (((suc n) * m) + n)
    ≡⟨ cong {ℕ} {ℕ} {suc n * m} {m + n * m} (λ x → (suc (x + n))) refl ⟩
      suc ((m + n * m) + n)
    ≡⟨ cong suc (sym (+-assoc m (n * m) n)) ⟩
      suc (m + (n * m + n))
    ≡⟨ cong (λ x → suc (m + x)) (+-comm' (n * m) n)⟩
      suc (m + (n + (n * m)))
    ≡⟨ cong (λ x → suc (m + x)) (*-suc n m) ⟩
      suc (m + n * suc m)
    ≡⟨ sym (m+1+n≡1+m+n m (n * suc m)) ⟩
      m + suc (n * suc m)
    ≡⟨ +-comm' m (suc (n * suc m)) ⟩
      suc (n * suc m + m)
    ≡⟨ cong suc (+-comm' (n * suc m) m) ⟩
      (suc n) * (suc m)
    ∎

  *-comm : ∀ m n → m * n ≡ n * m
  *-comm zero n = sym (n*0≡0 n)
  *-comm (suc m) n =
      n + m * n
    ≡⟨ cong (λ x → (n + x)) (*-comm m n)  ⟩
      n + n * m
    ≡⟨ *-suc n m ⟩
      n * suc m
    ∎

  -- Define the following functions:
  distribʳ-*-+ : ∀ a b c → (a + b) * c ≡ a * c + b * c
  distribʳ-*-+ zero b c = refl
  distribʳ-*-+ (suc a) b c =
      c + (a + b) * c
    ≡⟨ cong (λ x → c + x) (distribʳ-*-+ a b c) ⟩
      c + (a * c + b * c)
    ≡⟨ +-assoc c (a * c) (b * c) ⟩
      c + a * c + b * c
    ∎

  *-assoc : ∀ a b c → a * (b * c) ≡ (a * b) * c
  *-assoc zero b c = refl
  *-assoc (suc a) b c = -- (suc a) * (b * c) ≡ ((suc a) * b) * c
      b * c + (a * (b * c)) -- suc m * n = n + m * n
    ≡⟨ +-comm' (b * c) (a * (b * c)) ⟩
     a * (b * c) + b * c
    ≡⟨ cong (λ x → x + b * c) (*-assoc a b c) ⟩
      (a * b) * c + b * c
    ≡⟨ sym (distribʳ-*-+ (a * b) b c) ⟩
      (a * b + b) * c
    ≡⟨ cong (λ x → (x * c)) (+-comm' (a * b) b) ⟩
      (b + a * b) * c
    ∎

  -- (suc zero) * suc a === suc a (apply _*_)
  -- (suc a) + zero * (suc a) === suc a (apply _*_)
  -- suc a === suc a
  *-left-identity : ∀ a → 1 * a ≡ a
  *-left-identity zero = *-comm zero 1
  *-left-identity (suc a) =
      suc a + zero * suc a
    ≡⟨ cong (λ x → (suc a + x)) refl ⟩
      suc a + zero
    ∎

  -- (suc a) * 1 === (suc a)
  -- 1 + a * 1 === (suc a)
  -- suc (zero + a * 1) === (suc a)
  *-right-identity : ∀ a → a * 1 ≡ a
  *-right-identity zero = *-comm zero 1
  *-right-identity (suc a) = cong suc (*-right-identity a)
