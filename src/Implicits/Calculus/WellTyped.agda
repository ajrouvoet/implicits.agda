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
data _⊑_ {ν} : ∀ {p p'} → PolyType p ν → PolyType p' ν → Set where
  mono : ∀ {a b : Type ν} → a ≡ b → mono a ⊑ mono b
  poly-forall : ∀ {p p'} {a : PolyType p (suc ν)} {b : PolyType p' (suc ν)} → 
              a ⊑ b → ∀' a ⊑ ∀' b
  poly-instance : ∀ {p p'} {a : PolyType p (suc ν)} {b} {c : PolyType p' ν} → 
                  a free[/tp b ] ⊑ c → ∀' a ⊑ c

_⋢_ : ∀ {p ν} → PolyType p ν → PolyType p ν → Set
a ⋢ b = ¬ a ⊑ b

_Δ↝_ : ∀ {p ν n} (K : Ktx ν n) → PolyType p ν → Set

data ρ⟨_,_⟩↝_ {p ν n} (K : Ktx ν n) : ∀ {p'} → PolyType p ν → PolyType p' ν → Set where
  by-value : {a b : PolyType p ν} → a ⊑ b → ρ⟨ K , a ⟩↝ b
  yields : {a b : Type ν} {c : PolyType p ν} → K Δ↝ mono a → c ⊑ mono (a ⇒ b) → ρ⟨ K , c ⟩↝ mono b -- todo: not strictly positive

  -- it's easy to turn rules into functions
  -- as-func  : {a b c : Type ν} → (a →' b) ⊑ c → ρ⟨ K , a ⇒ b ⟩↝ c

-- implicit resolution is simply the first rule in the implicit context
-- that yields the queried type
Δ⟨_,_⟩=_ : ∀ {p p' ν n} → (Ktx ν n) → (a : PolyType p ν) → PolyType p' ν → Set
Δ⟨ (Γ , Δ) , a ⟩= r = first (ptype r) ∈ Δ ⇔ (λ r' → ρ⟨ (Γ , Δ) , proj₂ r' ⟩↝ a)

_Δ↝_ {ν = ν} K a = ∃₂ λ p (r : PolyType p ν) → Δ⟨ K , a ⟩= r

data _⊢_∈_ {ν n} (K : Ktx ν n) : ∀ {p} → Term ν n → PolyType p ν → Set where
  var : (x : Fin n) → K ⊢ var x ∈ proj₂ (lookup x (proj₁ K))
  λ' : ∀ {t b} a → (ptype $ mono a) ∷Γ K ⊢ t ∈ mono b → K ⊢ λ' a t ∈ mono (a →' b)
  Λ : ∀ {p t} {a : PolyType p (suc ν)} → ktx-weaken K ⊢ t ∈ a → K ⊢ Λ t ∈ ∀' a
  _[_] : ∀ {p t} {a : PolyType p (suc ν)} → 
         K ⊢ t ∈ ∀' a → (b : Type ν) → K ⊢ t [ b ] ∈ a free[/tp b ]
  _·_  : ∀ {f t a b} → K ⊢ f ∈ mono (a →' b) → K ⊢ t ∈ mono a → K ⊢ f · t ∈ mono b
  
  -- implicit abstract/application
  ρ : ∀ {t b} a → (ptype $ mono a) ∷Γ K ⊢ t ∈ mono b → K ⊢ ρ a t ∈ mono (a ⇒ b)
  _⟨⟩ : ∀ {t a b} → K ⊢ t ∈ mono (a ⇒ b) → K Δ↝ mono a → K ⊢ t ⟨⟩ ∈ mono b

  -- ML style let-polymorphism
  let'_in'_ : ∀ {p t u b} {a : PolyType p ν} → K ⊢ t ∈ a → (ptype a) ∷Γ K ⊢ u ∈ mono b → 
              K ⊢ (let' t in' u) ∈ mono b

  -- implicit binding
  implicit_in'_ : ∀ {p t u b} {a : PolyType p ν} → K ⊢ t ∈ a → (ptype a) ∷K K ⊢ u ∈ mono b → 
                  K ⊢ (implicit t in' u) ∈ mono b
  
_⊢_∉_ : ∀ {p ν n} → (K : Ktx ν n) → Term ν n → PolyType p ν → Set
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
