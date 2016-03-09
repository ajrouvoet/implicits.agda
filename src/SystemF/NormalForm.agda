module SystemF.NormalForm where

open import Prelude
open import SystemF.Syntax
open import SystemF.WellTyped
open import SystemF.Substitutions
open import Data.List hiding ([_])

mutual

  -- The eta-long beta-normal form described by Andreas Abel in:
  -- Abel, A., 2008, November.
  -- Weak βη-normalization and normalization by evaluation for System F.
  -- In Logic for Programming, Artificial Intelligence, and Reasoning (pp. 497-511).
  -- Springer Berlin Heidelberg.

  infix 4 _⊢_⇓_ _⊢_⇑_

  data _⊢_⇓_ {ν n} (Γ : Ctx ν n) : Term ν n → Type ν → Set where
    nvar   : ∀ n → Γ ⊢ (var n) ⇓ (lookup n Γ)
    napp  : ∀ {a b f e} → Γ ⊢ f ⇓ (a →' b) → Γ ⊢ e ⇑ a → Γ ⊢ (f · e) ⇓ b
    ntapp : ∀ {a f} b → Γ ⊢ f ⇓ (∀' a) → Γ ⊢ (f [ b ]) ⇓ a tp[/tp b ]

  data _⊢_⇑_ {ν n} (Γ : Ctx ν n) : Term ν n → Type ν → Set where
    nbase : ∀ {t a} → Base a → Γ ⊢ t ⇓ a → Γ ⊢ t ⇑ a
    nabs  : ∀ {a b e} → (a ∷ Γ) ⊢ e ⇑ b → Γ ⊢ (λ' a e) ⇑ (a →' b)
    ntabs : ∀ {a e} → (ctx-weaken Γ) ⊢ e ⇑ a → Γ ⊢ (Λ e) ⇑ (∀' a)

mutual

  ⇓-sound : ∀ {ν n} {Γ : Ctx ν n} {t a} → Γ ⊢ t ⇓ a → Γ ⊢ t ∈ a
  ⇓-sound (nvar n₁) = var n₁
  ⇓-sound (napp p x) = (⇓-sound p) · ⇑-sound x
  ⇓-sound (ntapp b p) = ⇓-sound p [ b ]

  ⇑-sound : ∀ {ν n} {Γ : Ctx ν n} {t a} → Γ ⊢ t ⇑ a → Γ ⊢ t ∈ a
  ⇑-sound (nbase a p) = ⇓-sound p
  ⇑-sound (nabs x) = λ' _ (⇑-sound x)
  ⇑-sound (ntabs x) = Λ (⇑-sound x)
