module Implicits.SystemF.SmallStep where

open import Prelude
open import Implicits.SystemF.WellTyped

infixl 4 _≻_

-- irreducible System F terms
data Value {ν n} : Term ν n → Set where
  λ' : ∀ τ t → Value (λ' τ t)
  Λ : ∀ t → Value (Λ t)

-- single step reduction of System F terms
data _≻_ {ν n} : Term ν n → Term ν n → Set where
  -- redexes
  reduce-[] : ∀ t a → (Λ t) [ a ] ≻ t tm[/tp a ]
  reduce-· : ∀ a t {u} → (λ' a t) · u ≻ t tm[/tm u ]

  -- contextual closure
  step-·₁ : ∀ {t t' u} → t ≻ t' → t · u ≻ t' · u
  step-·₂ : ∀ {t u u'} → u ≻ u' → t · u ≻ t · u'
  step-λ-body : ∀ {a t t'} → t ≻ t' → λ' a t ≻ λ' a t'
  step-Λ-body : ∀ {t t'} → t ≻ t' → Λ t ≻ Λ t'
  step-[] : ∀ {t t' a} → t ≻ t' → t [ a ] ≻ t' [ a ]

-- multi-step reductions
data _≻⋆_ {ν n} : Term ν n → Term ν n → Set where
  ≻-step : ∀ {t u} → t ≻ u → t ≻⋆ u
  ≻-trans : ∀ {t u v} → t ≻⋆ u → u ≻⋆ v → t ≻⋆ v

-- progress: welltyped terms are either values or can be reduced
progress : ∀ {ν τ} {t : Term ν 0} → [] ⊢ t ∈ τ → Value t ⊎ ∃ (_≻_ t)
progress (var ())
progress (Λ {t = t} ⊢t) = inj₁ (Λ t)
progress (λ' {t = t} a ⊢t) = inj₁ (λ' a t)
progress (_[_] ⊢t a) with progress ⊢t
progress (⊢t [ a ]) | inj₁ (λ' τ t) = {!!} -- cannot occur
progress (⊢t [ a ]) | inj₁ (Λ t) = inj₂ (, reduce-[] t a)
progress (⊢t [ a ]) | inj₂ (_ , y≻y') = inj₂ (, step-[] y≻y')
progress (⊢f · ⊢t) with progress ⊢f | progress ⊢t
progress (⊢f · ⊢t) | inj₁ (λ' τ t) | inj₁ y-isval = inj₂ (, reduce-· τ t)
progress (⊢f · ⊢t) | inj₁ (Λ t) | inj₁ y-isval = {!!} -- cannot occur
progress (_·_ {f = f} wf-f ⊢t) | _ | inj₂ (_ , y≻y') = inj₂ (, step-·₂ y≻y')
progress (_·_ {t = t} ⊢f ⊢t) | inj₂ (_ , f≻f') | _ = inj₂ (, step-·₁ f≻f')

-- preservation: reduction preserves well-typedness 
postulate ≻-preserves : ∀ {ν n} {Γ : Ctx ν n} {t t' τ} → Γ ⊢ t ∈ τ → t ≻ t' → Γ ⊢ t' ∈ τ
