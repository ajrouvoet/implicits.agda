module Implicits.SystemF.Terms.Constructors where

open import Prelude
open import Implicits.SystemF.Types
open import Implicits.SystemF.Terms
open import Implicits.SystemF.WellTyped
open import Implicits.SystemF.Substitutions.Lemmas
open import Implicits.SystemF.Types.Constructors

-- ml-normalized well-typed abstraction constructor
postulate λml : ∀ {ν n} {Γ : Ctx ν n} {b t} a → a ∷ Γ ⊢ t ∈ b → ∃ λ t' → Γ ⊢ t' ∈ (a →ml b)
{-
{b = tvar n₁} (tvar x) ⊢t = , λ' (tvar x) ⊢t
λml {b = b →' b₁} (tvar x) ⊢t = , λ' (tvar x) ⊢t
λml {b = ∀' b} (tvar x) ⊢t = {!!} -- ∀' (λml b (tm-weaken ⊢t))
λml {b = b} (a →' c) ⊢t = {!!}
λml (∀' a) ⊢t with λml a' wt' 
  where
    a' = ((tp-weaken a) tp[/tp (tvar zero) ])
    wt' = ?
λml (∀' a) ⊢t | u , wt-u = , ∀' wt-u
-}
