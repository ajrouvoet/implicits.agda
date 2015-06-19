{-# OPTIONS --no-positivity-check #-}
module Implicits.Syntactical.WellTyped where

open import Prelude hiding (id)
open import Data.Fin.Substitution
open import Implicits.Syntactical.Types public
open import Implicits.Syntactical.Terms public
open import Implicits.Syntactical.Contexts public
open import Extensions.ListFirst
open import Implicits.Syntactical.Substitutions

infixl 4 _⊢_∈_

infixl 4 _⊑_
data _⊑_ {ν} : PolyType ν → PolyType ν → Set where
  mono : ∀ {a b : Type ν} → a ≡ b → mono a ⊑ mono b
  poly-forall : ∀ {a : PolyType (suc ν)} {b : PolyType (suc ν)} → 
              a ⊑ b → ∀' a ⊑ ∀' b
  poly-instance : ∀ {a : PolyType (suc ν)} c {b : PolyType ν} → 
                  a pt[/pt c ] ⊑ b → ∀' a ⊑ b

_⋢_ : ∀ {ν} → PolyType ν → PolyType ν → Set
a ⋢ b = ¬ a ⊑ b

_Δ↝_ : ∀ {ν n} (K : Ktx ν n) → PolyType ν → Set

data ρ⟨_,_⟩↝_ {ν n} (K : Ktx ν n) : Binding ν → PolyType ν → Set where
  by-value : {a b : PolyType ν} → a ⊑ b → ρ⟨ K , val a ⟩↝ b
  -- todo: not strictly positive
  yields : {a b : Type ν} {a' b' : PolyType ν} → 
           K Δ↝ mono a → a' →ₚ b' ⊑ mono (a →' b) → ρ⟨ K , rule a' b' ⟩↝ mono b

  -- it's easy to turn rules into functions
  -- as-func  : {a b c : Type ν} → (a →' b) ⊑ c → ρ⟨ K , a ⇒ b ⟩↝ c

-- implicit resolution is simply the first rule in the implicit context
-- that yields the queried type
Δ⟨_,_⟩=_ : ∀ {ν n} → (Ktx ν n) → (a : PolyType ν) → Binding ν → Set
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
  _⟨⟩ : ∀ {t a b} → K ⊢ t ∈ mono (a →' b) → K Δ↝ mono a → K ⊢ t ⟨⟩ ∈ mono b

  -- ML style let-polymorphism
  let'_in'_ : ∀ {t u b} {a : PolyType ν} → K ⊢ t ∈ a → a ∷Γ K ⊢ u ∈ mono b → 
              K ⊢ (let' t in' u) ∈ mono b

  -- implicit binding
  implicit_in'_ : ∀ {t u b} {a : PolyType ν} → (wt : K ⊢ t ∈ a) → 
                  (val a) ∷K K ⊢ u ∈ mono b → K ⊢ (implicit t in' u) ∈ mono b
  implicit_⇒_in'_ : ∀ {t u c} {b : PolyType ν} → (a : PolyType ν) → (val a ∷K K) ⊢ t ∈ b → 
                    (rule a b) ∷K K ⊢ u ∈ mono c → K ⊢ (implicit a ⇒ t in' u) ∈ mono c
  
_⊢_∉_ : ∀ {ν n} → (K : Ktx ν n) → Term ν n → PolyType ν → Set
_⊢_∉_ K t τ = ¬ K ⊢ t ∈ τ

erase : ∀ {ν n} {K : Ktx ν n} {t a} → K ⊢ t ∈ a → Term ν n
erase {t = t} _ = t
