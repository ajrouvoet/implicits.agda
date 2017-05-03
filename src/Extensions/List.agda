module Extensions.List where

open import Prelude

open import Data.List

data _[_]=_ {a} {A : Set a} : List A → ℕ → A → Set where
  here : ∀ {x xs} → (x ∷ xs) [ 0 ]= x
  there : ∀ {x y xs n} → xs [ n ]= x → (y ∷ xs) [ suc n ]= x
