module Implicits.Syntactical.Contexts where

open import Prelude
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Implicits.Syntactical.Types
open import Implicits.Syntactical.Substitutions.Types

Ctx : ℕ → ℕ → Set
Ctx ν n = Vec (PolyType ν) n

data Binding ν : Set where
  rule : PolyType ν → PolyType ν → Binding ν
  val  : PolyType ν → Binding ν
  
totype : ∀ {ν} → Binding ν → PolyType ν
totype (rule a b) = a →ₚ b
totype (val x) = x

ICtx : ℕ → Set
ICtx ν = List.List (Binding ν)

Ktx : ℕ → ℕ → Set
Ktx ν n = Ctx ν n × ICtx ν

_∷Γ_ : ∀ {ν n} → PolyType ν → Ktx ν n → Ktx ν (suc n)
a ∷Γ (Γ , Δ) = (a ∷ Γ) , Δ

_∷Δ_ : ∀ {ν n} → Binding ν → Ktx ν n → Ktx ν n
a ∷Δ (Γ , Δ) = Γ , a List.∷ Δ

_∷K_ : ∀ {ν n} → Binding ν → Ktx ν n → Ktx ν (suc n)
rule a b ∷K (Γ , Δ) = (a →ₚ b) ∷ Γ , (rule a b) List.∷ Δ
val x ∷K (Γ , Δ) = x ∷ Γ , (val x) List.∷ Δ

nil : Ktx 0 0
nil = [] , List.[]
