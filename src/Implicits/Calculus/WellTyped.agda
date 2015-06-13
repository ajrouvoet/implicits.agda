{-# OPTIONS --no-positivity-check #-}
module Implicits.Calculus.WellTyped where

open import Prelude hiding (id)
open import Data.Fin.Substitution
open import Implicits.Calculus.Types public
open import Implicits.Calculus.Terms public
open import Implicits.Calculus.Contexts public
open import Extensions.ListFirst
open TypeSubst

infixl 4 _⊢_∈_

infixl 4 _⊑_
data _⊑_ {ν} : PolyType ν → PolyType ν → Set where
  mono : ∀ {a b : Type ν} → a ≡ b → mono a ⊑ mono b
  poly-forall : ∀ {a : PolyType (suc ν)} {b : PolyType (suc ν)} → 
              a ⊑ b → ∀' a ⊑ ∀' b
  poly-instance : ∀ {a : PolyType (suc ν)} {b} {c : PolyType ν} → 
                  a ptp[/tp b ] ⊑ c → ∀' a ⊑ c

_⋢_ : ∀ {ν} → PolyType ν → PolyType ν → Set
a ⋢ b = ¬ a ⊑ b

_Δ↝_ : ∀ {ν n} (K : Ktx ν n) → PolyType ν → Set

data ρ⟨_,_⟩↝_ {ν n} (K : Ktx ν n) : PolyType ν → PolyType ν → Set where
  by-value : {a b : PolyType ν} → a ⊑ b → ρ⟨ K , a ⟩↝ b
  yields : {a b : Type ν} {c : PolyType ν} → K Δ↝ mono a → c ⊑ mono (a ⇒ b) → ρ⟨ K , c ⟩↝ mono b -- todo: not strictly positive

  -- it's easy to turn rules into functions
  -- as-func  : {a b c : Type ν} → (a →' b) ⊑ c → ρ⟨ K , a ⇒ b ⟩↝ c

-- implicit resolution is simply the first rule in the implicit context
-- that yields the queried type
Δ⟨_,_⟩=_ : ∀ {ν n} → (Ktx ν n) → (a : PolyType ν) → PolyType ν → Set
Δ⟨ (Γ , Δ) , a ⟩= r = first r ∈ Δ ⇔ (λ r' → ρ⟨ (Γ , Δ) , r' ⟩↝ a)

_Δ↝_ {ν = ν} K a = ∃ λ (r : PolyType ν) → Δ⟨ K , a ⟩= r

data _⊢_∈_ {ν n} (K : Ktx ν n) : Term ν n → PolyType ν → Set where
  var : (x : Fin n) → K ⊢ var x ∈ (lookup x (proj₁ K))
  λ' : ∀ {t b} a → (mono a) ∷Γ K ⊢ t ∈ mono b → K ⊢ λ' a t ∈ mono (a →' b)
  Λ : ∀ {t} {a : PolyType (suc ν)} → ktx-weaken K ⊢ t ∈ a → K ⊢ Λ t ∈ ∀' a
  _[_] : ∀ {t} {a : PolyType (suc ν)} → 
         K ⊢ t ∈ ∀' a → (b : Type ν) → K ⊢ t [ b ] ∈ a ptp[/tp b ]
  _·_  : ∀ {f t a b} → K ⊢ f ∈ mono (a →' b) → K ⊢ t ∈ mono a → K ⊢ f · t ∈ mono b
  
  -- implicit abstract/application
  ρ : ∀ {t b} a → (mono a) ∷Γ K ⊢ t ∈ mono b → K ⊢ ρ a t ∈ mono (a ⇒ b)
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

{-
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
