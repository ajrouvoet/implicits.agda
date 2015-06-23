module Implicits.SystemF.Terms.Constructors where

open import Prelude
open import Data.Fin.Substitution
open import Implicits.SystemF.Types
open import Implicits.SystemF.Terms
open import Implicits.SystemF.WellTyped
open import Implicits.SystemF.Substitutions.Lemmas
open import Implicits.SystemF.Substitutions as S using ()
open import Implicits.SystemF.Types.Constructors

postulate ∀'-weaken-wt : ∀ {ν n} {Γ : Ctx ν n} {a t b} →
                         (∀' a) ∷ Γ ⊢ t ∈ b → a ∷ (ctx-weaken Γ) ⊢ tm-weaken t ∈ tp-weaken b

postulate blup : ∀ {ν n} {Γ : Ctx ν n} {a t b} →
                          (p : a ∷ Γ ⊢ t ∈ b) → (tp-weaken a ∷ ctx-weaken Γ ⊢ tm-weaken t ∈ tp-weaken b)
postulate lookup-wk≡tvar-lookup-varwk : ∀ {m} {n : Fin m} →
                                      lookup n (S.TypeSubst.wk {m}) ≡ tvar (lookup n (VarSubst.wk {m}))

-- {-# NO_TERMINATION_CHECK #-}
postulate ⊢λml : ∀ {ν n} {Γ : Ctx ν n} {b t} a → (⊢b : a ∷ Γ ⊢ t ∈ b) →
                 ∃ λ t' → Γ ⊢ t' ∈ (a →ml b)
{-
⊢λml {b = tvar n} (tvar x) ⊢t = , λ' (tvar x) ⊢t
⊢λml {b = a →' b} (tvar x) ⊢t = , λ' (tvar x) ⊢t
⊢λml {b = ∀' b} (tvar x) ⊢t with
  (⊢λml (tp-weaken (tvar x)) (blup ⊢t))
⊢λml {b = ∀' b} (tvar x) ⊢t | _ , ih = , Λ (ih [ tvar zero ])
⊢λml {b = tvar n₁} (a →' c) ⊢t = , λ' (a →' c) ⊢t
⊢λml {b = b →' b₁} (a →' c) ⊢t = , λ' (a →' c) ⊢t
⊢λml {b = ∀' b} (a →' c) ⊢t = {!!}
⊢λml (∀' a) ⊢t with (⊢λml a (∀'-weaken-wt ⊢t))
⊢λml (∀' a) ⊢t | _ , ih = , Λ ih
-}
