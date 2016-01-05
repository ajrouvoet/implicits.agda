module Implicits.Syntax.Type.Constructors (TC : Set) _tc≟_ where

open import Prelude
open import Implicits.Syntax.Type TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open TypeSubst

-- polymorphic identity
tid : ∀ {n} → Type n
tid = ∀' (simpl ((TVar zero) →' (TVar zero)))

-- type of bools encoding
tbool : Type 0
tbool = ∀' $ simpl ((TVar zero) →' (simpl ((TVar zero) →' (TVar zero))))

-- church numerals
tnat : Type 0
tnat = ∀' $ simpl ((simpl ((TVar zero) →' (TVar zero))) →' (simpl ((TVar zero) →' (TVar zero))))

-- existential quantification
∃' : ∀ {n} → (Type (suc n)) → Type n
∃' a = ∀' (∀' (simpl ((a tp/tp (wk ↑)) →' (simpl ((TVar (suc zero)) →' (TVar zero))))))

-- unit type
⊤' : ∀ {n} → Type n
⊤' = tid

-- zero type
⊥' : ∀ {n} → Type n
⊥' = ∀' (TVar zero)

-- n-ary function type
infixr 7 _→ⁿ_
_→ⁿ_ : ∀ {n k} → Vec (Type n) k → Type n → Type n
[]       →ⁿ z = z
(a ∷ as) →ⁿ z = as →ⁿ (simpl (a →' z))

-- Record/finite tuple
rec : ∀ {n k} → Vec (Type n) k → Type n
rec []       = ⊤'
rec (a ∷ as) = ∀' (simpl ((map tp-weaken (a ∷ as) →ⁿ TVar zero) →' TVar zero))

-- tuple
_×'_ : ∀ {n} → Type n → Type n → Type n
a ×' b = rec (a ∷ b ∷ [])
