open import Prelude hiding (lift; Fin′; subst; id)

module Implicits.Substitutions.Context (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Syntax.Type TC _tc≟_
open import Implicits.Syntax.Context TC _tc≟_
open import Implicits.Substitutions.Type TC _tc≟_ as TS using () 
open import Data.Fin.Substitution
open import Data.Star as Star hiding (map)
open import Data.Star.Properties

ktx-map : ∀ {ν μ n} → (Type ν → Type μ) →  Ktx ν n → Ktx μ n
ktx-map f (Γ , Δ) = map f Γ , List.map f Δ

_/_ : ∀ {ν μ n} → Ktx ν n → Sub Type ν μ → Ktx μ n
K / σ = ktx-map (λ t → t TS./ σ) K

_/Var_ : ∀ {ν m n} → Sub Fin n m → Ktx ν m → Ktx ν n
σ /Var (Γ , Δ) = map (λ x → lookup x Γ) σ , Δ

ictx-weaken : ∀ {ν} → ICtx ν → ICtx (suc ν)
ictx-weaken Δ = List.map (flip TS._/_ TS.wk) Δ

weaken : ∀ {ν n} → Ktx ν n → Ktx (suc ν) n
weaken K = K / TS.wk
