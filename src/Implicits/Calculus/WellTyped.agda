{-# OPTIONS --no-positivity-check #-}
module Implicits.Calculus.WellTyped (TC : Set) where

open import Prelude hiding (id)
open import Data.Fin.Substitution
open import Implicits.Calculus.Types TC public
open import Implicits.Calculus.Terms TC public
open import Implicits.Calculus.Contexts TC public
open import Extensions.ListFirst
open import Implicits.Calculus.Substitutions TC 
open Rules

infixl 4 _⊢_∈_

module TypeOrdering where

  infixl 4 _⊑_
  data _⊑_ {ν} : Type ν → Type ν → Set where
    poly-equal : ∀ {a b : Type ν} → a ≡ b → a ⊑ b
    poly-intro : ∀ {a : Type ν} {b : Type (suc ν)} →
                 tp-weaken a ⊑ b → a ⊑ ∀' b
    poly-elim : ∀ {a : Type (suc ν)} c {b : Type ν} → 
                a tp[/tp c ] ⊑ b → ∀' a ⊑ b

  _⋢_ : ∀ {ν} → Type ν → Type ν → Set
  a ⋢ b = ¬ a ⊑ b

open TypeOrdering public

_Δ↝_ : ∀ {ν n} (K : Ktx ν n) → Type ν → Set

-- The rules of implicit derivision.
-- This can be extended to support more complex derivations.
-- An example is the rule 'by-conversion' that allows implicit rules to be
-- used as implicit function values.
data ρ⟨_,_⟩↝_ {ν n} (K : Ktx ν n) : Type ν → Type ν → Set where
  -- base case
  by-value : (a : Type ν) → ρ⟨ K , a ⟩↝ a
  -- induction steps
  by-subsumption : ∀ {r a b : Type ν} →
                   ρ⟨ K , r ⟩↝ a →
                   a ⊑ b →
                   ρ⟨ K , r ⟩↝ b
  by-implication : ∀ {r a : Type ν} →
                   ρ⟨ K , r ⟩↝ a →
                   (a-rule : IsRule a) →
                   K Δ↝ (domain a-rule) → 
                   ρ⟨ K , r ⟩↝ codomain a-rule 
  by-composition : ∀ {b a : Type ν} →
                   (a-rule : IsRule a) →
                   ρ⟨ domain a-rule ∷K K , codomain a-rule ⟩↝ b →
                   ρ⟨ K , a ⟩↝ (domain a-rule ⇒ b)
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
  new : (c : TC) → K ⊢ new c ∈ tc c
  var : (x : Fin n) → K ⊢ var x ∈ (lookup x (proj₁ K))
  λ' : ∀ {t b} a → a ∷Γ K ⊢ t ∈ b → K ⊢ λ' a t ∈ (a →' b)
  Λ : ∀ {t} {a : Type (suc ν)} → ktx-weaken K ⊢ t ∈ a → K ⊢ Λ t ∈ ∀' a
  _[_] : ∀ {t} {a : Type (suc ν)} → 
         K ⊢ t ∈ ∀' a → (b : Type ν) → K ⊢ t [ b ] ∈ a tp[/tp b ]
  _·_  : ∀ {f t a b} → K ⊢ f ∈ (a →' b) → K ⊢ t ∈ a → K ⊢ f · t ∈ b
  
  -- implicit abstract/application
  ρ : ∀ {t b} a → (a) ∷K K ⊢ t ∈ b → K ⊢ ρ a t ∈ (a ⇒ b)
  _⟨_⟩ : ∀ {t a b} → K ⊢ t ∈ (a ⇒ b) → K Δ↝ a → K ⊢ t ⟨⟩ ∈ b

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
data _⊢ⁿ_∈_ {m n} (Γ : Ktx n m) :
  ∀ {k} → Vec (Term n m) k → Vec (Type n) k → Set where
    []  : Γ ⊢ⁿ [] ∈ []
    _∷_ : ∀ {t a k} {ts : Vec (Term n m) k} {as : Vec (Type n) k} →
          Γ ⊢ t ∈ a → Γ ⊢ⁿ ts ∈ as → Γ ⊢ⁿ t ∷ ts ∈ (a ∷ as)

-- Lookup a well-typed term in a collection thereof.
lookup-⊢ : ∀ {m n k} {Γ : Ktx n m} {ts : Vec (Term n m) k}
             {as : Vec (Type n) k} →
           (x : Fin k) → Γ ⊢ⁿ ts ∈ as → Γ ⊢ lookup x ts ∈ lookup x as
lookup-⊢ zero    (⊢t ∷ ⊢ts) = ⊢t
lookup-⊢ (suc x) (⊢t ∷ ⊢ts) = lookup-⊢ x ⊢ts
