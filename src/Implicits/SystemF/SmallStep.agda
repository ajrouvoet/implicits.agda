module Implicits.SystemF.SmallStep where

open import Prelude
open import Implicits.SystemF.WellTyped

infixl 4 _≻_

-- irreducible System F terms
data Value {ν n} : Term ν n → Set where
  λ'-value : ∀ {τ t} → Value (λ' τ t)
  Λ-value : ∀ {t} → Value (Λ t)

-- single step reduction of System F terms
data _≻_ {ν n} : Term ν n → Term ν n → Set where
  -- redexes
  reduce-[] : ∀ t a → (Λ t) [ a ] ≻ t tm[/tp a ]
  reduce-· : ∀ {t u a} → (λ' a t) · u ≻ t tm[/tm u ]

  -- contextual closure
  step-·₁ : ∀ {t t'} → t ≻ t' → ∀ u → t · u ≻ t' · u
  step-·₂ : ∀ {t u u'} → u ≻ u' → t · u ≻ t · u'
  step-λ-body : ∀ {a t t'} → t ≻ t' → λ' a t ≻ λ' a t'
  step-Λ-body : ∀ {t t'} → t ≻ t' → Λ t ≻ Λ t'
  step-[] : ∀ {t t' a} → t ≻ t' → (Λ t) [ a ] ≻ (Λ t') [ a ]

-- multi-step reductions
data _≻⋆_ {ν n} : Term ν n → Term ν n → Set where
  step : ∀ {t u} → t ≻ u → t ≻⋆ u
  trans : ∀ {t u v} → t ≻⋆ u → u ≻⋆ v → t ≻⋆ v

-- progress: welltyped terms are either values or can be reduced
progress : ∀ {ν τ} {t : Term ν 0} → [] ⊢ t ∈ τ → Value t ⊎ ∃ (_≻_ t)
progress (wt-var ())
progress (wt-Λ t) = inj₁ Λ-value
progress (wt-λ' a t) = inj₁ λ'-value
progress (wt-[] {t = t} (wt-Λ _) a) = inj₂ $ , reduce-[] t a
progress (wt-· f t) = inj₂ {!!}

-- preservation: reduction preserves well-typedness 
postulate ≻-preserves : ∀ {ν n} {Γ : Ctx ν n} {t t' τ} → Γ ⊢ t ∈ τ → t ≻ t' → Γ ⊢ t' ∈ τ
