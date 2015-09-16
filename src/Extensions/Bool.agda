module Extensions.Bool where

open import Data.Bool
open import Relation.Nullary public using (yes; no; ¬_; Dec)

is-yes : ∀ {a} {A : Set a} → Dec A → Bool
is-yes (yes p) = true
is-yes (no ¬p) = false
