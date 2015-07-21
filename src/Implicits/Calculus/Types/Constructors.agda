module Implicits.Calculus.Types.Constructors where

open import Prelude
open import Implicits.Calculus.Types 
open import Implicits.Calculus.Substitutions
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
