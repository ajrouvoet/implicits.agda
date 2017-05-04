module LFRef.Eval where

open import Prelude
open import Data.List

open import LFRef.Syntax
open import LFRef.Welltyped

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

  -- reductions
  ƛ-β : ∀ {t A e μ} → (ƛ A e) · t , μ ≻ (e exp/ (sub t)) , μ

  lett-β  : ∀ {t e μ} → (lett (tm t) e) , μ ≻ (e exp/ (sub t)) , μ

  ref-val : ∀ {t μ} → ref (tm t) , μ ≻ (tm (loc (length μ))) , (μ ∷ʳ t)

  assign-locval : ∀ {i x t μ} →
                  (p : i < length μ) →
                  --------------------------------------------
                  tm x ≔ (tm t) , μ ≻ (tm unit) , !store μ p t

  !-val : ∀ {i x μ} →
          (p : i < length μ) →
          -----------------------------------------
          ! (tm x) , μ ≻ tm (!load μ p) , μ

  -- contextual closure
  lett-clos₁ : ∀ {x e x' μ μ'} → x , μ ≻ x' , μ' → (lett x e) , μ ≻ (lett x' e) , μ'
  ref-clos : ∀ {e e' μ μ'} → e , μ ≻ e' , μ' → ref e , μ ≻ ref e' , μ'
  !-clos   : ∀ {e e' μ μ'} → e , μ ≻ e' , μ' → ! e , μ ≻ ! e' , μ'
  ≔-clos₁  : ∀ {x x' e μ μ'} → x , μ ≻ x' , μ' → x ≔ e , μ ≻ x' ≔ e , μ'
  ≔-clos₂  : ∀ {x e e' μ μ'} → e , μ ≻ e' , μ' → x ≔ e , μ ≻ x ≔ e' , μ'

-- Church-Rosser
-- diamond : ∀ {n} {u u' u'' : Term n} → u ≻ u' → u ≻ u'' → ∃ λ v → (u' ≻ v × u'' ≻ v)
-- church-rosser : ∀ {n} {u u' u'' : Term n} → u ≻⋆ u' → u ≻⋆ u'' → ∃ λ v → (u' ≻⋆ v × u'' ≻⋆ v)

-- reflexive-transitive closure of ≻
open import Data.Star
_≻⋆_ : ∀ {n} (c c' : Config n) → Set
c ≻⋆ c' = Star _≻_ c c'
