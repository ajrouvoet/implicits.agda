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
data _⊑_ {ν} : PolyType ν → PolyType ν → Set where
  poly-equal : ∀ {a b : PolyType ν} → a ≡ b → a ⊑ b
  poly-intro : ∀ {a : PolyType ν} {b : PolyType (suc ν)} →
               pt-weaken a ⊑ b → a ⊑ ∀' b
  poly-elim : ∀ {a : PolyType (suc ν)} c {b : PolyType ν} → 
              a pt[/tp c ] ⊑ b → ∀' a ⊑ b

_⋢_ : ∀ {ν} → PolyType ν → PolyType ν → Set
a ⋢ b = ¬ a ⊑ b

_Δ↝_ : ∀ {ν n} (K : Ktx ν n) → PolyType ν → Set

data ρ⟨_,_⟩↝_ {ν n} (K : Ktx ν n) : PolyType ν → PolyType ν → Set where
  -- base case
  by-value : {b : PolyType ν} → (a : PolyType ν) → ρ⟨ K , a ⟩↝ a
  -- induction steps
  by-subsumption : {r a b : PolyType ν} →
                   ρ⟨ K , r ⟩↝ a →
                   a ⊑ b →
                   ρ⟨ K , r ⟩↝ b
  by-implication : {r a : PolyType ν} →
                   ρ⟨ K , r ⟩↝ a →
                   (a-rule : IsRule a) →
                   K Δ↝ (domain a-rule) → 
                   ρ⟨ K , r ⟩↝ codomain a-rule 
  -- it's easy to turn rules into functions
  -- by-conversion : {u r : PolyType ν} →
                  -- ρ⟨ K , u ⟩↝ r →
                  -- (r-rule : IsRule r) → ρ⟨ K , u ⟩↝ to-function r-rule

-- implicit resolution is simply the first rule in the implicit context
-- that yields the queried type
Δ⟨_,_⟩=_ : ∀ {ν n} → (Ktx ν n) → (a : PolyType ν) → PolyType ν → Set
Δ⟨ (Γ , Δ) , a ⟩= r = first r ∈ Δ ⇔ (λ r' → ρ⟨ (Γ , Δ) , r' ⟩↝ a)

_Δ↝_ {ν = ν} K a = ∃ λ r → Δ⟨ K , a ⟩= r

data _⊢_∈_ {ν n} (K : Ktx ν n) : Term ν n → PolyType ν → Set where
  var : (x : Fin n) → K ⊢ var x ∈ (lookup x (proj₁ K))
  λ' : ∀ {t b} a → (mono a) ∷Γ K ⊢ t ∈ mono b → K ⊢ λ' a t ∈ mono (a →' b)
  Λ : ∀ {t} {a : PolyType (suc ν)} → ktx-weaken K ⊢ t ∈ a → K ⊢ Λ t ∈ ∀' a
  _[_] : ∀ {t} {a : PolyType (suc ν)} → 
         K ⊢ t ∈ ∀' a → (b : Type ν) → K ⊢ t [ b ] ∈ a pt[/tp b ]
  _·_  : ∀ {f t a b} → K ⊢ f ∈ mono (a →' b) → K ⊢ t ∈ mono a → K ⊢ f · t ∈ mono b
  
  -- implicit abstract/application
  ρ : ∀ {t b} a → (mono a) ∷K K ⊢ t ∈ mono b → K ⊢ ρ a t ∈ mono (a ⇒ b)
  _⟨⟩ : ∀ {t a b} → K ⊢ t ∈ mono (a ⇒ b) → K Δ↝ mono a → K ⊢ t ⟨⟩ ∈ mono b

  -- ML style let-polymorphism
  let'_in'_ : ∀ {t u b} {a : PolyType ν} → K ⊢ t ∈ a → a ∷Γ K ⊢ u ∈ mono b → 
              K ⊢ (let' t in' u) ∈ mono b

  -- implicit binding
  implicit_in'_ : ∀ {t u b} {a : PolyType ν} → K ⊢ t ∈ a → a ∷K K ⊢ u ∈ mono b → 
                  K ⊢ (implicit t in' u) ∈ mono b
  
_⊢_∉_ : ∀ {ν n} → (K : Ktx ν n) → Term ν n → PolyType ν → Set
_⊢_∉_ K t τ = ¬ K ⊢ t ∈ τ

erase : ∀ {ν n} {K : Ktx ν n} {t a} → K ⊢ t ∈ a → Term ν n
erase {t = t} _ = t
