module Functions.Dependent where

  open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_)
  open import Data.Fin using (Fin; zero; suc)
  open import Data.Vec using (Vec; []; _∷_)
  open import Data.Product using (_×_; _,_)

  fromℕ : (n : ℕ) → Fin (suc n)
  fromℕ zero = zero  -- Note: different zeros
  fromℕ (suc n) = suc (fromℕ n)

  -- Define a substraction with restricted domain:
  _-_ : (n : ℕ) → Fin (suc n) → ℕ
  zero - zero = zero
  zero - (suc ())
  (suc n) - zero = (suc n)
  (suc n) - (suc x) = n - x

  -- Define toℕ:
  toℕ : ∀ {n} → Fin n → ℕ
  toℕ zero = zero
  toℕ (suc x) = suc (toℕ x)

  -- Define fromℕ≤ such that toℕ (fromℕ≤ e) is m if e : m < n:
  fromℕ≤ : ∀ {m n} → m < n → Fin n
  fromℕ≤ {zero} {zero} ()
  fromℕ≤ {zero} {suc n} _ = zero
  fromℕ≤ {suc m} {zero} ()
  fromℕ≤ {suc m} {suc n} (s≤s rel) = suc (fromℕ≤ rel)

  -- Define inject+ such that toℕ (inject+ n i) is the same as toℕ i:
  inject+ : ∀ {m} n → Fin m → Fin (m + n)
  inject+ {zero} zero ()
  inject+ {zero} (suc m) ()
  inject+ {suc m} n zero = zero
  inject+ {suc m} n (suc x) = suc (inject+ n x)

  -- Define four such that toℕ four is 4:
  four : Fin 66
  four = suc (suc (suc (suc zero)))

  two : ℕ
  two = (suc (suc zero))








  -- Type of `inject+ two four` is `Fin 68`
  -- Value of `inject+ two four` is (suc (suc (suc (suc zero)))) (4 in the Fin 68 set)

  -- Define raise such that toℕ (raise n i) is the same as n + toℕ i:
  raise : ∀ {m} n → Fin m → Fin (n + m)
  raise {zero} zero ()
  raise {zero} (suc n) ()
  raise {suc n} zero i = i
  raise {suc n} (suc m) i = suc (raise m i)

  -- Define head and tail.
  head : ∀ {n}{A : Set} → Vec A (suc n) → A
  head (x ∷ xs) = x

  tail : ∀ {n}{A : Set} → Vec A (suc n) → Vec A n
  tail (x ∷ xs) = xs

  -- Define concatenation for vectors.
  _++_ : ∀ {n m}{A : Set} → Vec A n → Vec A m → Vec A (n + m)
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  -- Define maps. (Note that two cases will be enough!)
  maps : ∀ {n}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
  maps [] [] = []
  maps (f ∷ fs) (x ∷ xs) = f x ∷ (maps fs xs)

  -- Define replicate.
  replicate : ∀ {n}{A : Set} → A → Vec A n
  replicate {zero} _ = []
  replicate {suc n} a = a ∷ (replicate {n} a)

  -- Define map with the help of maps and replicate.
  map : ∀ {n}{A B : Set} → (A → B) → Vec A n → Vec B n
  map f = maps (replicate f)

  -- Define zip with the help of map and maps.
  zip : ∀ {n}{A B : Set} → Vec A n → Vec B n → Vec (A × B) n
  zip [] [] = []
  zip xs ys = maps (map _,_ xs) ys

  -- Define safe element indexing.
  _!_ : ∀ {n}{A : Set} → Vec A n → Fin n → A
  (x ∷ xs) ! zero = x
  (x ∷ xs) ! (suc n) = xs ! n
