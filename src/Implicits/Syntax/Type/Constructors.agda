module Implicits.Oliveira.Types.Constructors (TC : Set) where

open import Prelude
open import Implicits.Oliveira.Types TC
open import Implicits.Oliveira.Substitutions TC
open TypeSubst

-- polymorphic identity
tid : ∀ {n} → Type n
tid = ∀' $ (tvar zero) →' (tvar zero)

-- type of bools encoding
tbool : Type 0
tbool = ∀' $ (tvar zero) →' (tvar zero) →' (tvar zero)

-- church numerals
tnat : Type 0
tnat = ∀' $ ((tvar zero) →' (tvar zero)) →' (tvar zero) →' (tvar zero)

-- existential quantification
∃' : ∀ {n} → (Type (suc n)) → Type n
∃' a = ∀' (∀' ((a tp/tp (wk ↑)) →' (tvar (suc zero))) →' (tvar zero))

-- unit type
⊤' : ∀ {n} → Type n
⊤' = tid

-- zero type
⊥' : ∀ {n} → Type n
⊥' = ∀' $ (tvar zero)

-- n-ary function type
infixr 7 _→ⁿ_
_→ⁿ_ : ∀ {n k} → Vec (Type n) k → Type n → Type n
[]       →ⁿ z = z
(a ∷ as) →ⁿ z = as →ⁿ a →' z

-- Record/finite tuple
rec : ∀ {n k} → Vec (Type n) k → Type n
rec []       = ⊤'
rec (a ∷ as) = ∀' ((map tp-weaken (a ∷ as) →ⁿ tvar zero) →' tvar zero)

-- tuple
_×'_ : ∀ {n} → Type n → Type n → Type n
a ×' b = rec (a ∷ b ∷ [])
