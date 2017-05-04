module LFRef.Eval where

open import Prelude
open import Data.List

open import LFRef.Syntax
open import LFRef.Welltyped

-- small steps for terms
infix 1 _≻ₜ_
data _≻ₜ_ {n} : (t t' : Term n) → Set where
  -- beta reduction
  ƛ-β : ∀ {A x b} → ((ƛ A x) · b) ≻ₜ (x / (sub b))

  -- closure
  ƛ-clos : ∀ {A e e'} → e ≻ₜ e' → (ƛ A e) ≻ₜ (ƛ A e')
  ·-clos₁ : ∀ {e t t'} → t ≻ₜ t' → (t · e) ≻ₜ (t' · e)
  ·-clos₂ : ∀ {e e' t} → e ≻ₜ e' → (t · e) ≻ₜ (t · e')

open import Data.Star
open import Data.Sum
open import Data.Product

-- reflexive-transitive closure of _≻ₜ_
_≻ₜ⋆_ : ∀ {n} (t t' : Term n) → Set
t ≻ₜ⋆ t' = Star _≻ₜ_ t t'

-- term equality in terms of reductions
_≡tm_ : ∀ {n} → (a b : Term n) → Set
a ≡tm b = a ≻ₜ⋆ b ⊎ b ≻ₜ⋆ a

-- machine configuration: expression to reduce and a store
Config : ℕ → Set
Config n = Exp n × Store n

!load : ∀ {n i} → (μ : Store n) → i < length μ → Term n
!load {i = i} [] ()
!load {i = zero} (x ∷ μ) (s≤s p) = x
!load {i = suc i} (x ∷ μ) (s≤s p) = !load μ p


!store : ∀ {n i} → (μ : Store n) → i < length μ → Term n → Store n
!store [] () v
!store {i = zero} (x ∷ μ) (s≤s p) v = v ∷ μ
!store {i = suc i} (x ∷ μ) (s≤s p) v = v ∷ (!store μ p v)

-- small steps for expressions
infix 1 _≻_
data _≻_ {n} : (t t' : Config n) → Set where

  -- β-reduction
  lett-β  : ∀ {t e μ} → (lett (tm t) e) , μ ≻ (e exp/ (sub t)) , μ
  ref-val : ∀ {t μ} → ref (tm t) , μ ≻ (tm (loc (length μ))) , (μ ∷ʳ t)
  assign-locval : ∀ {i t μ} → (p : i < length μ) → tm (loc i) ≔ (tm t) , μ ≻ (tm unit) , !store μ p t
  !-loc : ∀ {i μ} → (p : i < length μ) → ! (tm (loc i)) , μ ≻ tm (!load μ p) , μ

  -- contextual closure
  tm-clos : ∀ {t t' μ} → t ≻ₜ t' → (tm t) , μ ≻ (tm t') , μ

  lett-clos₁ : ∀ {t t' μ} → t ≻ₜ t' → (tm t) , μ ≻ (tm t') , μ
  lett-clos₂ : ∀ {t t' μ} → t ≻ₜ t' → (tm t) , μ ≻ (tm t') , μ

  ref-clos : ∀ {e e' μ μ'} → e , μ ≻ e' , μ' → ref e , μ ≻ ref e' , μ'
  !-clos   : ∀ {e e' μ μ'} → e , μ ≻ e' , μ' → ! e , μ ≻ ! e' , μ'
  ≔-clos₁  : ∀ {x x' e μ μ'} → x , μ ≻ x' , μ' → x ≔ e , μ ≻ x' ≔ e , μ'
  ≔-clos₂  : ∀ {x e e' μ μ'} → e , μ ≻ e' , μ' → x ≔ e , μ ≻ x ≔ e' , μ'

-- Church-Rosser
-- diamond : ∀ {n} {u u' u'' : Term n} → u ≻ u' → u ≻ u'' → ∃ λ v → (u' ≻ v × u'' ≻ v)
-- church-rosser : ∀ {n} {u u' u'' : Term n} → u ≻⋆ u' → u ≻⋆ u'' → ∃ λ v → (u' ≻⋆ v × u'' ≻⋆ v)
