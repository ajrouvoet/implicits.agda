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
  poly-equal : ∀ {a b : PolyType ν} → a ≡ b → a ⊑ b
  poly-intro : ∀ {a : PolyType ν} {b : PolyType (suc ν)} →
               pt-weaken a ⊑ b → a ⊑ ∀' b
  poly-elim : ∀ {a : PolyType (suc ν)} c {b : PolyType ν} → 
              a pt[/tp c ] ⊑ b → ∀' a ⊑ b

_⋢_ : ∀ {ν} → PolyType ν → PolyType ν → Set
a ⋢ b = ¬ a ⊑ b

_Δ↝_ : ∀ {ν n} (K : Ktx ν n) → PolyType ν → Set

-- The rules of implicit derivision.
-- This can be extended to support more complex derivations.
-- An example is the rule 'by-conversion' that allows implicit rules to be
-- used as implicit function values.
data ρ⟨_,_⟩↝_ {ν n} (K : Ktx ν n) : Implicit ν → PolyType ν → Set where
  -- base case
  by-value : (a : PolyType ν) → ρ⟨ K , val a ⟩↝ a
  by-implication : {a : PolyType ν} {r : IsFunction a} →
                   K Δ↝ (domain r) → 
                   ρ⟨ K , rule r ⟩↝ codomain r
  -- induction steps
  by-subsumption : {r : Implicit ν} {a b : PolyType ν} →
                   ρ⟨ K , r ⟩↝ a →
                   a ⊑ b →
                   ρ⟨ K , r ⟩↝ b
  -- it's easy to turn rules into functions
  -- by-conversion : {u r : PolyType ν} →
                  -- ρ⟨ K , u ⟩↝ r →
                  -- (r-rule : IsFunction r) → ρ⟨ K , u ⟩↝ to-function r-rule

-- implicit resolution is simply the first rule in the implicit context
-- that yields the queried type
Δ⟨_,_⟩=_ : ∀ {ν n} → (Ktx ν n) → (a : PolyType ν) → Implicit ν → Set
Δ⟨ (Γ , Δ) , a ⟩= r = first r ∈ Δ ⇔ (λ r' → ρ⟨ (Γ , Δ) , r' ⟩↝ a)

_Δ↝_ {ν = ν} K a = ∃ λ r → Δ⟨ K , a ⟩= r

mutual

  -- judgement whether a binding is well formed
  data _⊢_wfi {ν n} (K : Ktx ν n) : ImplicitTerm ν n → Set where
    val  : ∀ {t a} → (⊢t : K ⊢ t ∈ a) → K ⊢ val t wfi
    rule : ∀ {t a} → (⊢t : K ⊢ t ∈ a) → (fa : IsFunction a) → K ⊢ rule t wfi

  ⊢wfi-to-implicit : ∀ {ν n} {K : Ktx ν n} {b} → K ⊢ b wfi → Implicit ν
  ⊢wfi-to-implicit (val {a = a} x) = val a
  ⊢wfi-to-implicit (rule ⊢t a-func) = rule a-func

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
    implicit_in'_ : ∀ {e a b} →
                    (wfi : K ⊢ a wfi) → (⊢wfi-to-implicit wfi) ∷K K ⊢ e ∈ mono b →
                    K ⊢ (implicit a in' e) ∈ mono b
  
_⊢_∉_ : ∀ {ν n} → (K : Ktx ν n) → Term ν n → PolyType ν → Set
_⊢_∉_ K t τ = ¬ K ⊢ t ∈ τ

erase : ∀ {ν n} {K : Ktx ν n} {t a} → K ⊢ t ∈ a → Term ν n
erase {t = t} _ = t
