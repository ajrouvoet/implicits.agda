module Implicits.Calculus.WellTyped where

open import Prelude
open import Data.Fin.Substitution
open import Implicits.Calculus.Types public
open import Implicits.Calculus.Terms public
open import Implicits.Calculus.Contexts public

infix 4 _⊢_∈_

data _Δ↝_ {ν n} (K : Ktx ν n) : Type ν → Set where
  

data _⊢_∈_ {ν n} (K : Ktx ν n) : Term ν n → Type ν → Set where
  var : (x : Fin n) → K ⊢ var x ∈ lookup x (proj₁ K)
  Λ : ∀ {t a} → (ktx-weaken K) ⊢ t ∈ a → K ⊢ Λ t ∈ ∀' a
  λ' : ∀ {t b} a → a ∷Γ K ⊢ t ∈ b → K ⊢ λ' a t ∈ a →' b
  _[_] : ∀ {t a} → K ⊢ t ∈ ∀' a → (b : Type ν) → K ⊢ t [ b ] ∈ a tp[/tp b ]
  _·_  : ∀ {f t a b} → K ⊢ f ∈ (a →' b) → K ⊢ t ∈ a → K ⊢ f · t ∈ b
  
  -- implicit abstract/application
  ρ : ∀ {t b} a → a ∷Γ K ⊢ t ∈ b → K ⊢ ρ a t ∈ a ⇒ b
  _⟨⟩ : ∀ {t a b} → K ⊢ t ∈ a ⇒ b → K Δ↝ a → K ⊢ t ⟨⟩ ∈ b

  -- implicit binding
  implicit_in'_ : ∀ {t u a b} → K ⊢ t ∈ a → a ∷K K ⊢ u ∈ b → K ⊢ (implicit t in' u) ∈ b
  
_⊢_∉_ : ∀ {ν n} → (K : Ktx ν n) → Term ν n → Type ν → Set
_⊢_∉_ K t τ = ¬ K ⊢ t ∈ τ
  
{-
⊢erase : ∀ {ν n} {Γ : Ctx ν n} {t τ} → Γ ⊢ t ∈ τ → Term ν n
⊢erase (var x) = var x
⊢erase (Λ {t} x) = Λ t
⊢erase (λ' {t} a x) = λ' a t
⊢erase (_[_] {t} x b) = t
⊢erase (_·_ {f} x x₁) = f

⊢f·a-inversion : ∀ {ν n f t b} {Γ : Ctx ν n} → Γ ⊢ f · t ∈ b → 
                 ∃ λ a → Γ ⊢ f ∈ a →' b × Γ ⊢ t ∈ a
⊢f·a-inversion (_·_ f∈a→b t∈a) = , (f∈a→b , t∈a)

⊢tc[a]-inversion : ∀ {ν n tc a' b} {Γ : Ctx ν n} → Γ ⊢ tc [ b ] ∈ a' → ∃ λ a → Γ ⊢ tc ∈ ∀' a
⊢tc[a]-inversion (_[_] tc∈∀'a b) = , tc∈∀'a

unique-type : ∀ {ν n} {Γ : Ctx ν n} {t τ τ'} → Γ ⊢ t ∈ τ → Γ ⊢ t ∈ τ' → τ ≡ τ'
unique-type (var x) (var .x) = refl
unique-type (Λ l) (Λ r) = cong ∀' (unique-type l r)
unique-type (λ' a l) (λ' .a r) = cong (λ b → a →' b) (unique-type l r)
unique-type (l [ b ]) (r [ .b ]) = cong (λ{ (∀' fa) → fa tp[/tp b ]; a → a}) (unique-type l r)
unique-type (f · e) (f' · e') = cong (λ{ (a →' b) → b; a → a }) (unique-type f f')

unique-type′ : ∀ {ν n} {Γ : Ctx ν n} {t τ τ'} → Γ ⊢ t ∈ τ → τ ≢ τ' → Γ ⊢ t ∉ τ'
unique-type′ ⊢t∈τ neq ⊢t∈τ' = neq $ unique-type ⊢t∈τ ⊢t∈τ'
  
postulate tm[/tp]-preserves : ∀ {ν n} {Γ : Ctx ν n} {t τ} → 
                            Γ ⊢ Λ t ∈ ∀' τ → ∀ a → Γ ⊢ (t tm[/tp a ]) ∈ τ tp[/tp a ]
postulate tm[/tm]-preserves : ∀ {ν n} {Γ : Ctx ν n} {t u a b} → 
                            b ∷ Γ ⊢ t ∈ a → Γ ⊢ u ∈ b → Γ ⊢ (t tm[/tm u ]) ∈ a

-}
