module Functions.Cases where

  open import Sets.Enumerated using (Bool; true; false)

  not : Bool → Bool
  not true  = false
  not false = true

  infixr 6 _∧_
  _∧_   : Bool → Bool → Bool
  true  ∧ x = x
  false ∧ _ = false

  infixr 5 _∨_
  _∨_   : Bool → Bool → Bool
  true  ∨ _ = true
  false ∨ x = x

  _∨`_   : Bool → Bool → Bool
  x ∨` y = not ((not x) ∧ (not y))

  -- Define a set named Answer with three elements, yes, no and maybe.
  data Answer : Set where
    yes   : Answer
    no    : Answer
    maybe : Answer

  -- Define logical operations on Answer!
  a-not : Answer → Answer
  a-not yes   = no
  a-not no    = yes
  a-not maybe = maybe

  _a-∧_   : Answer → Answer → Answer
  yes   a-∧ x = x
  no    a-∧ _ = no
  maybe a-∧ _ = maybe

  _a-∨_   : Answer → Answer → Answer
  yes   a-∨ _ = yes
  no    a-∨ x = x
  maybe a-∨ _ = maybe

  -- Define a set named Quarter with four elements, east, west, north and south.
  data Quarter : Set where
    east  : Quarter
    west  : Quarter
    north : Quarter
    south : Quarter

  -- Define a function turnLeft : Quarter → Quarter.
  turnLeft : Quarter → Quarter
  turnLeft east = north
  turnLeft west = south
  turnLeft north = west
  turnLeft south = east

  -- Define the functions turnBack and turnRight with the help of turnLeft! (by
  -- either pattern matching or defining a specific function composition
  -- function).
  turnBack : Quarter → Quarter
  turnBack x = turnLeft (turnLeft x)

  turnRight : Quarter → Quarter
  turnRight x = turnLeft (turnBack x)
