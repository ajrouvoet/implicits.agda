module Effects.WellTyped where

open import Prelude
open import Effects.Terms
open import Effects.Substitutions

infixl 7 _⊢_∈_&_
data _⊢_∈_&_ {ν η n : ℕ} (Γ : Ctx ν η n) : Term ν η n → Type ν η → Effect η → Set where
  var : ∀ {n} → Γ ⊢ var n ∈ (lookup n Γ) & Pure

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
  H : ∀ {t a e} → ctx-ef-weaken Γ ⊢ t ∈ tp-ef-weaken a & e → Γ ⊢ H t ∈ a & H e
  _!_ : ∀ {t a e} → Γ ⊢ t ∈ a & H e → (f : Effect η) → Γ ⊢ (t ! f) ∈ a & e [/ef f ]
  
  -- the effectful primitives
  print : Γ ⊢ print ∈ void & IO
  throw : Γ ⊢ throw ∈ void & Throws
  write : Γ ⊢ write ∈ void & Writes
  read  : Γ ⊢ read ∈ void & Reads
