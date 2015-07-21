{-# OPTIONS --no-positivity-check #-}
module Implicits.Calculus.WellTyped where

open import Prelude hiding (id)
open import Data.Fin.Substitution
open import Implicits.Calculus.Types public
open import Implicits.Calculus.Terms public
open import Implicits.Calculus.Contexts public
open import Extensions.ListFirst
open import Implicits.Calculus.Substitutions
open Rules

infixl 4 _⊢_∈_

infixl 4 _⊑_
data _⊑_ {ν} : Type ν → Type ν → Set where
  poly-equal : ∀ {a b : Type ν} → a ≡ b → a ⊑ b
  poly-intro : ∀ {a : Type ν} {b : Type (suc ν)} →
               tp-weaken a ⊑ b → a ⊑ ∀' b
  poly-elim : ∀ {a : Type (suc ν)} c {b : Type ν} → 
              a tp[/tp c ] ⊑ b → ∀' a ⊑ b

_⋢_ : ∀ {ν} → Type ν → Type ν → Set
a ⋢ b = ¬ a ⊑ b

_Δ↝_ : ∀ {ν n} (K : Ktx ν n) → Type ν → Set

-- The rules of implicit derivision.
-- This can be extended to support more complex derivations.
-- An example is the rule 'by-conversion' that allows implicit rules to be
-- used as implicit function values.
data ρ⟨_,_⟩↝_ {ν n} (K : Ktx ν n) : Type ν → Type ν → Set where
  -- base case
  by-value : (a : Type ν) → ρ⟨ K , a ⟩↝ a
  -- induction steps
  by-subsumption : {r a b : Type ν} →
                   ρ⟨ K , r ⟩↝ a →
                   a ⊑ b →
                   ρ⟨ K , r ⟩↝ b
  by-implication : {r a : Type ν} →
                   ρ⟨ K , r ⟩↝ a →
                   (a-rule : IsRule a) →
                   K Δ↝ (domain a-rule) → 
                   ρ⟨ K , r ⟩↝ codomain a-rule 
  -- it's easy to turn rules into functions
  -- by-conversion : {u r : Type ν} →
                  -- ρ⟨ K , u ⟩↝ r →
                  -- (r-rule : IsRule r) → ρ⟨ K , u ⟩↝ to-function r-rule

-- implicit resolution is simply the first rule in the implicit context
-- that yields the queried type
Δ⟨_,_⟩=_ : ∀ {ν n} → (Ktx ν n) → (a : Type ν) → Type ν → Set
Δ⟨ (Γ , Δ) , a ⟩= r = first r ∈ Δ ⇔ (λ r' → ρ⟨ (Γ , Δ) , r' ⟩↝ a)

_Δ↝_ {ν = ν} K a = ∃ λ r → Δ⟨ K , a ⟩= r

data _⊢_∈_ {ν n} (K : Ktx ν n) : Term ν n → Type ν → Set where
  var : (x : Fin n) → K ⊢ var x ∈ (lookup x (proj₁ K))
  λ' : ∀ {t b} a → a ∷Γ K ⊢ t ∈ b → K ⊢ λ' a t ∈ (a →' b)
  Λ : ∀ {t} {a : Type (suc ν)} → ktx-weaken K ⊢ t ∈ a → K ⊢ Λ t ∈ ∀' a
  _[_] : ∀ {t} {a : Type (suc ν)} → 
         K ⊢ t ∈ ∀' a → (b : Type ν) → K ⊢ t [ b ] ∈ a tp[/tp b ]
  _·_  : ∀ {f t a b} → K ⊢ f ∈ (a →' b) → K ⊢ t ∈ a → K ⊢ f · t ∈ b
  
  -- implicit abstract/application
  ρ : ∀ {t b} a → (a) ∷K K ⊢ t ∈ b → K ⊢ ρ a t ∈ (a ⇒ b)
  _⟨⟩ : ∀ {t a b} → K ⊢ t ∈ (a ⇒ b) → K Δ↝ a → K ⊢ t ⟨⟩ ∈ b

  -- ML style let-polymorphism
  let'_in'_ : ∀ {t u b} {a : Type ν} → K ⊢ t ∈ a → a ∷Γ K ⊢ u ∈ b → 
              K ⊢ (let' t in' u) ∈ b

  -- implicit binding
  implicit_in'_ : ∀ {t u b} {a : Type ν} → K ⊢ t ∈ a → a ∷K K ⊢ u ∈ b → 
                  K ⊢ (implicit t in' u) ∈ b
  
_⊢_∉_ : ∀ {ν n} → (K : Ktx ν n) → Term ν n → Type ν → Set
_⊢_∉_ K t τ = ¬ K ⊢ t ∈ τ

erase : ∀ {ν n} {K : Ktx ν n} {t a} → K ⊢ t ∈ a → Term ν n
erase {t = t} _ = t
