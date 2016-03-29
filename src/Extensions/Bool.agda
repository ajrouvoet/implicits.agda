module Extensions.Bool where

open import Data.Bool
open import Relation.Nullary public using (yes; no; ¬_; Dec)

is-yes : ∀ {a} {A : Set a} → Dec A → Bool
is-yes (yes p) = true
is-yes (no ¬p) = false

data AllTrue {p} (P : Set p) : Bool → Set p where
  true  : P → AllTrue P true
  false : AllTrue P false

all-map : ∀ {p} {P Q : Set p} {b} → AllTrue P b → (f : P → Q) → AllTrue Q b
all-map (true x) f = true (f x)
all-map false f = false
