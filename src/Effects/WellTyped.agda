module Effects.WellTyped where

open import Prelude
open import Effects.Terms public
open import Effects.Substitutions

infixl 7 _⊢_∈_&_
data _⊢_∈_&_ {ν η n : ℕ} (Γ : Ctx ν η n) : Term ν η n → Type ν η → Effect η → Set where
  var : ∀ x → Γ ⊢ var x ∈ (lookup x Γ) & Pure

  -- value abstraction & application
  λ'  : ∀ {b t e} →
          (a : Type ν η) →
          (a ∷ Γ) ⊢ t ∈ b & e →
          Γ ⊢ (λ' a t) ∈ (a →[ e ] b) & Pure

  _·_ : ∀ {f t a b eₗ e₁ e₂} →
          (Γ ⊢ f ∈ (a →[ eₗ ] b) & e₁) → (Γ ⊢ t ∈ a & e₂) →
          Γ ⊢ f · t ∈ b & (eₗ ∪ e₁ ∪ e₂)

  -- type abstraction & application
  Λ    : ∀ {e a} → ctx-tp-weaken Γ ⊢ e ∈ a & Pure → Γ ⊢ Λ e ∈ ∀' a & Pure
  _[_] : ∀ {f e a} → Γ ⊢ f ∈ ∀' a & e → (b : Type ν η) → Γ ⊢ f [ b ] ∈ a [/tp b ] & e

  -- effect abstraction & application
  H : ∀ {t a e} → ctx-ef-weaken Γ ⊢ t ∈ a & e → Γ ⊢ H t ∈ H a & H e
  _!_ : ∀ {t a e} → Γ ⊢ t ∈ a & H e → (f : Effect η) → Γ ⊢ (t ! f) ∈ a & e [/ef f ]
  
  -- the effectful primitives
  print : Γ ⊢ print ∈ unit & IO
  throw : Γ ⊢ throw ∈ unit & Throws
  write : Γ ⊢ write ∈ unit & Writes
  read  : Γ ⊢ read ∈ unit & Reads

  -- primitive terms
  tt : Γ ⊢ tt ∈ unit & Pure
