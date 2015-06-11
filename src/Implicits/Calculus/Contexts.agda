module Implicits.Calculus.Contexts where

open import Prelude
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Implicits.Calculus.Types

Ctx : ℕ → ℕ → Set
Ctx ν n = Vec (PType ν) n

ICtx : ℕ → Set
ICtx ν = List.List (PType ν)

Ktx : ℕ → ℕ → Set
Ktx ν n = Ctx ν n × ICtx ν

_∷Γ_ : ∀ {ν n} → PType ν → Ktx ν n → Ktx ν (suc n)
a ∷Γ (Γ , Δ) = (a ∷ Γ) , Δ

_∷Δ_ : ∀ {ν n} → PType ν → Ktx ν n → Ktx ν n
a ∷Δ (Γ , Δ) = Γ , a List.∷ Δ

_∷K_ : ∀ {ν n} → PType ν → Ktx ν n → Ktx ν (suc n)
a ∷K (Γ , Δ) = a ∷ Γ , a List.∷ Δ

nil : Ktx 0 0
nil = [] , List.[]

module CtxSubst where
  
  postulate _/_ : ∀ {ν μ n} → Ctx ν n → Sub Type ν μ → Ctx μ n
  -- Γ / σ = map (λ s → s TypeSubst./ σ) Γ
  
  ctx-weaken : ∀ {ν n} → Ctx ν n → Ctx (suc ν) n
  ctx-weaken Γ = Γ / TypeSubst.wk
  
  postulate ktx-weaken : ∀ {ν n} → Ktx ν n → Ktx (suc ν) n
  -- ktx-weaken (Γ , Δ) = (ctx-weaken Γ , List.map (λ t → t TypeSubst./ TypeSubst.wk) Δ)

open CtxSubst public renaming (_/_ to _ctx-/_)
