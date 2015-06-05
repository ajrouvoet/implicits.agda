module Extensions.Vec where

open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality public hiding ([_])

lookup⋆map : ∀ {a b : Set} {n} (v : Vec a n) (f : a → b) x → 
             f (lookup x v) ≡ lookup x (map f v)
lookup⋆map [] f ()
lookup⋆map (x ∷ xs) f zero = refl
lookup⋆map (x ∷ xs) f (suc y) = lookup⋆map xs f y

∷⋆map : ∀ {a b : Set} {n} (f : a → b) (x : a) (xs : Vec a n) → map f (x ∷ xs) ≡ f x ∷ (map f xs)
∷⋆map f x [] = refl
∷⋆map f x (y ∷ xs) = cong (_∷_ (f x)) (∷⋆map f y xs)
