open import Prelude hiding (id)

module Implicits.Oliveira.WellTyped (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Extensions.ListFirst
open import Implicits.Oliveira.Substitutions TC _tc≟_

module TypingRules (_⊢ᵣ_ : ∀ {ν n} → Ktx ν n → Type ν → Set) where
  infixl 6 _⊢unamb_
  infixl 4 _⊢_∈_ 

  data _⊢unamb_ {ν} : List (Fin ν) → Type ν → Set where
    ua-simp : ∀ {a l} → l List.⊆ fvars a → l ⊢unamb a
    ua-tabs : ∀ {a l} → zero List.∈ l →
              List.gfilter (λ{ (Fin.zero) → nothing; (suc n) → just n}) l ⊢unamb (∀' a)
    ui-iabs : ∀ {a b l} → List.[] ⊢unamb a → l ⊢unamb b → l ⊢unamb (a ⇒ b)

  data _⊢_∈_ {ν n} (K : Ktx ν n) : Term ν n → Type ν → Set where
    new : (c : TC) → K ⊢ new c ∈ simpl (tc c)
    var : (x : Fin n) → K ⊢ var x ∈ (lookup x (proj₁ K))
    λ' : ∀ {t b} a → a ∷Γ K ⊢ t ∈ b → K ⊢ λ' a t ∈ simpl (a →' b)
    Λ : ∀ {t} {a : Type (suc ν)} → ktx-weaken K ⊢ t ∈ a → K ⊢ Λ t ∈ ∀' a
    _[_] : ∀ {t} {a : Type (suc ν)} → 
           K ⊢ t ∈ ∀' a → (b : Type ν) → K ⊢ t [ b ] ∈ a tp[/tp b ]
    _·_  : ∀ {f t a b} → K ⊢ f ∈ simpl (a →' b) → K ⊢ t ∈ a → K ⊢ f · t ∈ b

    -- implicit abstract/application
    ρ : ∀ {t b a} → List.[] ⊢unamb a → a ∷K K ⊢ t ∈ b → K ⊢ ρ a t ∈ (a ⇒ b)
    _⟨_⟩ : ∀ {t ρ a b} → K ⊢ ρ ∈ (a ⇒ b) → K ⊢ t ∈ a → K ⊢ ρ ⟨ t ⟩ ∈ b
    ¿ : ∀ {a} → List.[] ⊢unamb a → K ⊢ᵣ a → K ⊢ ¿ a ∈ a

    -- ML style let-polymorphism
    let'_in'_ : ∀ {t u b} {a : Type ν} → K ⊢ t ∈ a → a ∷Γ K ⊢ u ∈ b → 
                K ⊢ (let' t in' u) ∈ b

    -- implicit binding
    implicit_in'_ : ∀ {t u b} {a : Type ν} → K ⊢ t ∈ a → a ∷K K ⊢ u ∈ b → 
                    K ⊢ (implicit t in' u) ∈ b

  _⊢_∉_ : ∀ {ν n} → (K : Ktx ν n) → Term ν n → Type ν → Set
  _⊢_∉_ K t τ = ¬ K ⊢ t ∈ τ

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
