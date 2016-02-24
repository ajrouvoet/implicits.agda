open import Prelude hiding (id)

module Implicits.WellTyped where

open import Data.Fin.Substitution
open import Implicits.Syntax.Type
open import Implicits.Syntax.Term
open import Implicits.Syntax.Context
open import Implicits.Substitutions

module TypingRules (_⊢ᵣ_ : ∀ {ν} → ICtx ν → Type ν → Set) where
  infixl 6 _⊢unamb_
  infixl 4 _⊢_∈_ 

  data _⊢unamb_ {ν} : List (Fin ν) → Type ν → Set where
    ua-simp : ∀ {a l} → l List.⊆ fvars a → l ⊢unamb a
    ua-tabs : ∀ {a l} → zero List.∈ l →
              List.gfilter (λ{ (Fin.zero) → nothing; (suc n) → just n}) l ⊢unamb (∀' a)
    ui-iabs : ∀ {a b l} → List.[] ⊢unamb a → l ⊢unamb b → l ⊢unamb (a ⇒ b)

  -----------------------------------------------------------------------------
  -- typings

  data _⊢_∈_ {ν n} (K : Ktx ν n) : Term ν n → Type ν → Set where
    var : (x : Fin n) → K ⊢ var x ∈ (lookup x (proj₁ K))
    λ' : ∀ {t b} a → a ∷Γ K ⊢ t ∈ b → K ⊢ λ' a t ∈ simpl (a →' b)
    Λ : ∀ {t} {a : Type (suc ν)} → ktx-weaken K ⊢ t ∈ a → K ⊢ Λ t ∈ ∀' a
    _[_] : ∀ {t} {a : Type (suc ν)} → 
           K ⊢ t ∈ ∀' a → (b : Type ν) → K ⊢ t [ b ] ∈ a tp[/tp b ]
    _·_  : ∀ {f t a b} → K ⊢ f ∈ simpl (a →' b) → K ⊢ t ∈ a → K ⊢ f · t ∈ b

    -- implicit abstract/application
    ρ : ∀ {t b} a → a ∷K K ⊢ t ∈ b → K ⊢ ρ a t ∈ (a ⇒ b)
    _⟨_⟩ : ∀ {a b f} → K ⊢ f ∈ a ⇒ b → (proj₂ K) ⊢ᵣ a → K ⊢ f ⟨⟩ ∈ b
    _with'_ : ∀ {r e a b} → K ⊢ r ∈ a ⇒ b → K ⊢ e ∈ a → K ⊢ r with' e ∈ b

  _⊢_∉_ : ∀ {ν n} → (K : Ktx ν n) → Term ν n → Type ν → Set
  _⊢_∉_ K t τ = ¬ K ⊢ t ∈ τ

  -----------------------------------------------------------------------------
  -- syntactic sugar

  let'_in'_ : ∀ {ν n} {e₁ : Term ν n} {e₂ : Term ν (suc n)} {a b} {K} →
              K ⊢ e₁ ∈ a → a ∷Γ K ⊢ e₂ ∈ b → K ⊢ (let' e₁ ∶ a in' e₂) ∈ b
  let' e₁ in' e₂ = (λ' _ e₂) · e₁

  implicit'_in'_ : ∀ {ν n} {e₁ : Term ν n} {e₂ : Term ν (suc n)} {a b} {K} →
              K ⊢ e₁ ∈ a → a ∷K K ⊢ e₂ ∈ b → K ⊢ (implicit e₁ ∶ a in' e₂) ∈ b
  implicit' e₁ in' e₂ = (ρ _ e₂) with' e₁

  wt-¿ : ∀ {ν n} {r : Type ν} {K : Ktx ν n} → (proj₂ K) ⊢ᵣ r → K ⊢ (¿ r) ∈ r
  wt-¿ {r = r} x = (ρ r (var zero)) ⟨ x ⟩

  -----------------------------------------------------------------------------
  -- utilities

  erase : ∀ {ν n} {K : Ktx ν n} {t a} → K ⊢ t ∈ a → Term ν n
  erase {t = t} _ = t

  -- Collections of typing derivations for well-typed terms.
  data _⊢ⁿ_∈_ {m n} (Γ : Ktx n m) : ∀ {k} → Vec (Term n m) k → Vec (Type n) k → Set where
    []  : Γ ⊢ⁿ [] ∈ []
    _∷_ : ∀ {t a k} {ts : Vec (Term n m) k} {as : Vec (Type n) k} →
        Γ ⊢ t ∈ a → Γ ⊢ⁿ ts ∈ as → Γ ⊢ⁿ t ∷ ts ∈ (a ∷ as)

  -- Lookup a well-typed term in a collection thereof.
  lookup-⊢ : ∀ {m n k} {Γ : Ktx n m} {ts : Vec (Term n m) k} {as : Vec (Type n) k} →
              (x : Fin k) → Γ ⊢ⁿ ts ∈ as → Γ ⊢ lookup x ts ∈ lookup x as
  lookup-⊢ zero  (⊢t ∷ ⊢ts) = ⊢t
  lookup-⊢ (suc x) (⊢t ∷ ⊢ts) = lookup-⊢ x ⊢ts
