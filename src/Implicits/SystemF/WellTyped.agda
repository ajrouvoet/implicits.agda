module Implicits.SystemF.WellTyped where

open import Prelude
open import Implicits.SystemF.Types public
open import Implicits.SystemF.Terms public
open import Implicits.SystemF.Contexts public

infix 4 _⊢_∈_

data _⊢_∈_ {ν n} (Γ : Ctx ν n) : Term ν n → Type ν → Set where
  wt-var : (x : Fin n) → Γ ⊢ var x ∈ lookup x Γ
  wt-Λ   : ∀ {t a} → (ctx-weaken Γ) ⊢ t ∈ a → Γ ⊢ Λ t ∈ ∀' a
  wt-λ'  : ∀ {t b} → (a : Type ν) → a ∷ Γ ⊢ t ∈ b → Γ ⊢ λ' a t ∈ a →' b
  wt-[]  : ∀ {t a} → Γ ⊢ t ∈ ∀' a → (b : Type ν) → Γ ⊢ t [ b ] ∈ a tp-[/ b ]
  wt-·   : ∀ {f t a b} → Γ ⊢ f ∈ (a →' b) → Γ ⊢ t ∈ a → Γ ⊢ f · t ∈ b

⊢f·a-inversion : ∀ {ν n f t b} {Γ : Ctx ν n} → Γ ⊢ f · t ∈ b → 
                 ∃ λ a → Γ ⊢ f ∈ a →' b × Γ ⊢ t ∈ a
⊢f·a-inversion (wt-· f∈a→b t∈a) = , (f∈a→b , t∈a)

⊢tc[a]-inversion : ∀ {ν n tc a' b} {Γ : Ctx ν n} → Γ ⊢ tc [ b ] ∈ a' → ∃ λ a → Γ ⊢ tc ∈ ∀' a
⊢tc[a]-inversion (wt-[] tc∈∀'a b) = , tc∈∀'a
