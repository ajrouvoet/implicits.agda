module Implicits.Calculus.Contexts (TypeConstant : Set) where

open import Prelude
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Implicits.Calculus.Types TypeConstant 

Ctx : ℕ → ℕ → Set
Ctx ν n = Vec (Type ν) n

ICtx : ℕ → Set
ICtx ν = List.List (Type ν)

Ktx : ℕ → ℕ → Set
Ktx ν n = Ctx ν n × ICtx ν

_∷Γ_ : ∀ {ν n} → Type ν → Ktx ν n → Ktx ν (suc n)
a ∷Γ (Γ , Δ) = (a ∷ Γ) , Δ

_∷Δ_ : ∀ {ν n} → Type ν → Ktx ν n → Ktx ν n
a ∷Δ (Γ , Δ) = Γ , a List.∷ Δ

_∷K_ : ∀ {ν n} → Type ν → Ktx ν n → Ktx ν (suc n)
a ∷K (Γ , Δ) = a ∷ Γ , a List.∷ Δ

nil : ∀ {ν} → Ktx ν 0
nil = [] , List.[]
