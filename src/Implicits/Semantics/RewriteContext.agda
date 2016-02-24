open import Prelude

module Implicits.Semantics.RewriteContext where

open import Implicits.Syntax
open import Implicits.Substitutions
open import Implicits.Substitutions.Lemmas

-- rewrite context (relation between implicit and explicit context)
_#_ : ∀ {ν n} (Γ : Ctx ν n) (Δ : ICtx ν) → Set
Γ # Δ = All (λ i → i ∈ Γ) Δ

K# : ∀ {ν n} (K : Ktx ν n) → Set
K# (Γ , Δ) = Γ # Δ

#tvar : ∀ {ν n} {K : Ktx ν n} → K# K → K# (ktx-weaken K)
#tvar All.[] = All.[]
#tvar (px All.∷ K#K) = (∈⋆map px (λ t → t tp/tp TypeLemmas.wk)) All.∷ (#tvar K#K)

#var : ∀ {ν n} {K : Ktx ν n} → (a : Type ν) → K# K → K# (a ∷Γ K)
#var a All.[] = All.[]
#var a (px All.∷ K#K) = there px All.∷ (#var a K#K)

#ivar : ∀ {ν n} {K : Ktx ν n} → (a : Type ν) → K# K → K# (a ∷K K)
#ivar a K#K = here All.∷ (All.map there K#K)
