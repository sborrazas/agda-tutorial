module Sets.Enumerated where

  data Bool : Set where
    true  : Bool
    false : Bool

  data Answer : Set where
    yes   : Answer
    no    : Answer
    maybe : Answer

  data Quarter : Set where
    east  : Quarter
    west  : Quarter
    north : Quarter
    south : Quarter

  data ⊥ : Set where   -- There is no constructor.

  data ⊤ : Set where
    tt : ⊤
