open import Prelude

module Implicits.Syntax.Context where

open import Implicits.Syntax.Type
open import Data.List.All

Ctx : ℕ → ℕ → Set
Ctx ν n = Vec (Type ν) n

ICtx : ℕ → Set
ICtx ν = List.List (Type ν)

-- wellformed implicit contexts
_⊢OK : ∀ {ν} → ICtx ν → Set
Δ ⊢OK = All (λ a → List.[] ⊢unamb a) Δ

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
