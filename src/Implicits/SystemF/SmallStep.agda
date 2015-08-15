module Implicits.SystemF.SmallStep (TC : Set) where

open import Prelude
open import Implicits.SystemF.WellTyped TC
open import Implicits.SystemF.Substitutions TC
open import Implicits.SystemF.Substitutions.Lemmas TC

infixl 4 _≻_

-- irreducible System F terms
data Value {ν n} : Term ν n → Set where
  λ' : ∀ τ t → Value (λ' τ t)
  Λ : ∀ t → Value (Λ t)
  new : ∀ c → Value (new c)

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
 
∀'-value-lemma : ∀ {ν n} {Γ : Ctx ν n} {t a} → Γ ⊢ t ∈ ∀' a → Value t → ∃ λ e → t ≡ Λ e
∀'-value-lemma () (λ' τ t)
∀'-value-lemma () (new c)
∀'-value-lemma (Λ t∈∀a) (Λ t) = t , refl

→'-value-lemma : ∀ {ν n} {Γ : Ctx ν n} {t a b} → Γ ⊢ t ∈ a →' b → Value t → 
                 ∃ λ e → (t ≡ λ' a e) × a ∷ Γ ⊢ e ∈ b
→'-value-lemma () (Λ t)
→'-value-lemma () (new c)
→'-value-lemma (λ' a ⊢t∈a→b) (λ' .a t) = t , refl , ⊢t∈a→b

-- progress: welltyped terms are either values or can be reduced
progress : ∀ {ν τ} {t : Term ν 0} → [] ⊢ t ∈ τ → Value t ⊎ ∃ (_≻_ t)
progress (var ())
progress (new c) = inj₁ (new c)
progress (Λ {t = t} ⊢t) = inj₁ (Λ t)
progress (λ' {t = t} a ⊢t) = inj₁ (λ' a t)
progress (_[_] ⊢t a) with progress ⊢t

-- we can rule out the possibility that t is both well typed and a value, 
-- but not a lambda
-- leaving only cases that can make progress
progress (_[_] ⊢t a ) | inj₁ (λ' τ t') with ∀'-value-lemma ⊢t (λ' τ t') 
progress (() [ a ]) | inj₁ (λ' τ t') | t≡Λe
progress (⊢t [ a ]) | inj₁ (new c) with ∀'-value-lemma ⊢t (new c)
progress (() [ a ]) | inj₁ (new c) | t≡Λe
progress (⊢t [ a ]) | inj₁ (Λ t) = inj₂ (, reduce-[] t a)
progress (⊢t [ a ]) | inj₂ (_ , y≻y') = inj₂ (, step-[] y≻y')

-- similar to above
progress (⊢f · ⊢t) with progress ⊢f | progress ⊢t
progress (⊢f · ⊢t) | inj₁ (λ' τ t) | inj₁ y-isval = inj₂ (, reduce-· τ t)
progress (⊢f · ⊢t) | inj₁ (Λ t) | inj₁ y-isval with →'-value-lemma ⊢f (Λ t)
progress (() · ⊢t) | inj₁ (Λ t) | inj₁ y-isval | f≡a→'b
progress (⊢f · ⊢t) | inj₁ (new t) | inj₁ y-isval with →'-value-lemma ⊢f (new t)
progress (() · ⊢t) | inj₁ (new t) | inj₁ y-isval | f≡a→'b
progress (_·_ {f = f} wf-f ⊢t) | _ | inj₂ (_ , y≻y') = inj₂ (, step-·₂ y≻y')
progress (_·_ {t = t} ⊢f ⊢t) | inj₂ (_ , f≻f') | _ = inj₂ (, step-·₁ f≻f')

-- preservation: reduction preserves well-typedness 
≻-preserves : ∀ {ν n} {Γ : Ctx ν n} {t t' τ} → Γ ⊢ t ∈ τ → t ≻ t' → Γ ⊢ t' ∈ τ
≻-preserves (var x) ()
≻-preserves (new c) ()
≻-preserves (Λ ⊢t) (step-Λ-body t≻t') = Λ (≻-preserves ⊢t t≻t')
≻-preserves (λ' a ⊢t) (step-λ-body t≻t') = λ' a (≻-preserves ⊢t t≻t')
-- goal: (Λ t) [ a ] and t tm[/tp a ] have the same type
≻-preserves (⊢t [ a ]) (reduce-[] t .a) = WtTypeLemmas.tm[/tp]-preserves ⊢t a
≻-preserves (⊢t [ a ]) (step-[] t≻t') = (≻-preserves ⊢t t≻t') [ a ]
-- goal: (λ' a t) · u and t tm[/tm u ] have the same type
≻-preserves (λ' a ⊢t · ⊢u) (reduce-· .a t₁) = WtTermLemmas.tm[/tm]-preserves ⊢t ⊢u
≻-preserves (⊢t · ⊢u) (step-·₁ t≻t') = (≻-preserves ⊢t t≻t') · ⊢u
≻-preserves (⊢t · ⊢u) (step-·₂ u≻u') = ⊢t · (≻-preserves ⊢u u≻u')
