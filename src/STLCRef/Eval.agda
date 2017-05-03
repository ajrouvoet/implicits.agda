module STLCRef.Eval where

open import Prelude

open import Data.Product
open import Data.List
open import Data.List.Reverse
open import Data.Nat
open import Data.Fin hiding (_<_)

open import STLCRef.Syntax
open import STLCRef.Welltyped

_!!_ : ∀ {n i} → (μ : Store n) → i < length μ → ∃ (Val {n})
_!!_ {i = i} [] ()
_!!_ {i = zero} (x ∷ μ) (s≤s p) = x
_!!_ {i = suc i} (x ∷ μ) (s≤s p) = μ !! p

!store : ∀ {n i e} → (μ : Store n) → i < length μ → Val {n} e → Store n
!store [] () v
!store {i = zero} (x ∷ μ) (s≤s p) v = (, v) ∷ μ
!store {i = suc i} (x ∷ μ) (s≤s p) v = x ∷ (!store μ p v)

Config : (n : ℕ) → Set
Config n = Exp n × Store n

infixl 1 _≻_
data _≻_ : ∀ {n} → Config n → Config n → Set where

  ---------------------------------------
  -- Reduction rules
  ---------------------------------------

  -- β
  AppAbs : ∀ {n} {A x} {e : Exp (suc n)} {μ : Store n} →
           ---------------------------------
           (ƛ A e) · x , μ ≻ e / (sub x) , μ

  -- new
  RefVal : ∀ {n e} {μ : Store n} →
           (v : Val e) →
           --------------------------------------------
           (ref e , μ) ≻ (loc (length μ) , μ ∷ʳ (, v))

  -- load
  DerefLoc : ∀ {n i} {μ : Store n} →
             (p : i < length μ) →
             ---------------------------------------------------
             (! (loc i) , μ) ≻ (proj₁ (μ !! p) , μ)

  -- store
  Assign : ∀ {i n e} {μ : Store n} →
           (p : i < length μ) →
           (v : Val e) →
           ----------------------------------------------
           loc i ≔ e , μ ≻ unit , !store μ p v

  ---------------------------------------
  -- contextual closure
  ---------------------------------------

  Ref : ∀ {n e'} {e : Exp n} {μ μ'} →
        (e , μ) ≻ (e' , μ') →
        ---------------------------------------
        (ref e) , μ ≻ (ref e') , μ'

  Appₗ : ∀ {n f' e} {f : Exp n} {μ μ'} →
         (f , μ) ≻ (f' , μ') →
         ---------------------------------------
         (f · e) , μ ≻ (f' · e) , μ'

  Appᵣ : ∀ {n e' e} {f : Exp n} {μ μ'} →
         (e , μ) ≻ (e' , μ') →
         ---------------------------------------
         (f · e) , μ ≻ (f · e') , μ'

  Deref : ∀ {n} {e : Exp n} {e'} {μ μ'} →
          e , μ ≻ e' , μ' →
          ---------------------------------------
          ! e , μ ≻ ! e' , μ'

  Assign₁ : ∀ {n} {e₁ : Exp n} {e₁' e₂} {μ μ'} →
            e₁ , μ ≻ e₁' , μ' →
            ---------------------------------------
            e₁ ≔ e₂ , μ ≻ e₁' ≔ e₂ , μ'

  Assign₂ : ∀ {n} {e₁ : Exp n} {e₂' e₂} {μ μ'} →
            e₂ , μ ≻ e₂' , μ' →
            ---------------------------------------
            e₁ ≔ e₂ , μ ≻ e₁ ≔ e₂' , μ'

------------------------------------------------
-- Reflexive-transitive closure of step relation
------------------------------------------------

open import Data.Star

infixl 1 _≻*_
_≻*_ : ∀ {n} → Config n → Config n → Set
c ≻* c' = Star _≻_ c c'
