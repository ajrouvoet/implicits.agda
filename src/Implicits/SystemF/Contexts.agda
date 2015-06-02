module Implicits.SystemF.Contexts where

open import Prelude
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Implicits.SystemF.Types

Ctx : ℕ → ℕ → Set
Ctx ν n = Vec (Type ν) n

module CtxSubst where
  
  _/_ : ∀ {ν μ n} → Ctx ν n → Sub Type ν μ → Ctx μ n
  Γ / σ = Γ TypeSubst.⊙ σ
  
  ctx-weaken : ∀ {ν n} → Ctx ν n → Ctx (suc ν) n
  ctx-weaken Γ = Γ / TypeSubst.wk

open CtxSubst public renaming (_/_ to _ctx-/_)
