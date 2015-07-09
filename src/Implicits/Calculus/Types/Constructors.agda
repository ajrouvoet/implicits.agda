module Implicits.Calculus.Types.Constructors where

open import Prelude
open import Implicits.Calculus.Types 
open import Implicits.Calculus.Substitutions
open TypeSubst

-- polymorphic identity
tid : ∀ {n} → PolyType n
tid = ∀' $ mono $ (tvar zero) →' (tvar zero)

-- type of bools encoding
tbool : PolyType 0
tbool = ∀' $ mono $ (tvar zero) →' (tvar zero) →' (tvar zero)

-- church numerals
tnat : PolyType 0
tnat = ∀' $ mono $ ((tvar zero) →' (tvar zero)) →' (tvar zero) →' (tvar zero)

-- existential quantification
∃' : ∀ {n} → (PolyType (suc n)) → PolyType n
∃' a = ∀' (∀' ((a pt/tp (wk ↑)) →ₚ (mono $ tvar (suc zero))) →ₚ mono (tvar zero))

-- unit type
⊤' : ∀ {n} → PolyType n
⊤' = tid

-- zero type
⊥' : ∀ {n} → PolyType n
⊥' = ∀' $ mono $ (tvar zero)
