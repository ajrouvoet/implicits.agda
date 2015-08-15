open import Prelude

module Effects.WellTyped (EC : Set) (_ec≟_ : Decidable {A = EC} _≡_ ) where

open import Effects.Terms EC _ec≟_ public
open import Effects.Substitutions EC _ec≟_

infixl 7 _⊢_∈_+_
data _⊢_∈_+_ {ν η n : ℕ} (Γ : Ctx ν η n) : Term ν η n → Type ν η → Effects η → Set where
  var : ∀ x → Γ ⊢ var x ∈ (lookup x Γ) + pure

  -- value abstraction + application
  λ'  : ∀ {b t e} →
          (a : Type ν η) →
          (a ∷ Γ) ⊢ t ∈ b + e →
          Γ ⊢ (λ' a t) ∈ (a →[ e ] b) + pure

  _·_ : ∀ {f t a b eₗ e₁ e₂} →
          (Γ ⊢ f ∈ (a →[ eₗ ] b) + e₁) → (Γ ⊢ t ∈ a + e₂) →
          Γ ⊢ f · t ∈ b + (eₗ ∪ e₁ ∪ e₂)

  -- type abstraction + application
  Λ    : ∀ {e a} → ctx-tp-weaken Γ ⊢ e ∈ a + pure → Γ ⊢ Λ e ∈ ∀' a + pure
  _[_] : ∀ {f e a} → Γ ⊢ f ∈ ∀' a + e → (b : Type ν η) → Γ ⊢ f [ b ] ∈ a [/tp b ] + e

  -- effect abstraction + application
  H : ∀ {t a} → ctx-ef-weaken Γ ⊢ t ∈ a + pure → Γ ⊢ H t ∈ H a + pure
  _!_ : ∀ {t a e} → Γ ⊢ t ∈ H a + e → (f : Effects η) → Γ ⊢ (t ! f) ∈ a tp[/ef f ] + e

  -- the effectful primitives
  does : (c : EC) → Γ ⊢ does c ∈ unit + List.[ has c ]

  -- primitive terms
  tt : Γ ⊢ tt ∈ unit + pure

effects : ∀ {ν η n} {Γ : Ctx ν η n} {t a e} → Γ ⊢ t ∈ a + e → Effects η
effects {e = e} _ = e

erase : ∀ {ν η n} {Γ : Ctx ν η n} {t a e} → Γ ⊢ t ∈ a + e → Type ν η
erase {a = a} _ = a

