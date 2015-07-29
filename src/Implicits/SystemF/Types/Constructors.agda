module Implicits.SystemF.Types.Constructors (TC : Set) where

open import Prelude
open import Implicits.SystemF.Types TC
open import Implicits.SystemF.Substitutions.Types TC

-- church numerals
tnat : Type 0
tnat = ∀' (((tvar zero) →' (tvar zero)) →' (tvar zero) →' (tvar zero))

-- Type of the polymorphic identity
tid' : ∀ {n} → Type n
tid' = ∀' ((tvar zero) →' (tvar zero))

-- Top/terminal/unit type
⊤' : ∀ {n} → Type n
⊤' = tid'

-- Bottom/initial/zero type
⊥' : ∀ {n} → Type n
⊥' = ∀' (tvar zero)

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
