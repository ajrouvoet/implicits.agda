module Impure.STLCRef.Welltyped where

open import Prelude
open import Data.Nat
open import Data.Vec
open import Data.List
open import Data.Fin hiding (_<_)
open import Extensions.List as L using ()

open import Impure.STLCRef.Syntax

-- store typings
World : Set
World = List Type

_⊢loc_∶_ : World → ℕ → Type → Set
Σ ⊢loc i ∶ A = Σ L.[ i ]= A

Ctx : (n : ℕ) → Set
Ctx n = Vec Type n

data _,_⊢_∶_ : ∀ {n} → Ctx n → World → Exp n → Type → Set where
  unit : ∀ {n} {Γ : Ctx n} {Σ} →
         ---------------------------------------
         Γ , Σ ⊢ unit ∶ Unit

  var  : ∀ {n i A} {Γ : Ctx n} {Σ} →
         Γ [ i ]= A →
         ---------------------------------------
         Γ , Σ ⊢ var i ∶ A

  loc : ∀ {n i A} {Γ : Ctx n} {Σ} →
         Σ ⊢loc i ∶ A →
         ---------------------------------------
         Γ , Σ ⊢ loc i ∶ Ref A

  ƛ   : ∀ {n e A B} {Γ : Ctx n} {Σ} →
         (A ∷ Γ) , Σ ⊢ e ∶ B →
         ---------------------------------------
         Γ , Σ ⊢ (ƛ A e) ∶ (A ⇒ B)

  _·_ : ∀ {n f x A B} {Γ : Ctx n} {Σ} →
         Γ , Σ ⊢ f ∶ (A ⇒ B) →
         Γ , Σ ⊢ x ∶ A →
         ---------------------------------------
         Γ , Σ ⊢ (f · x) ∶ B

  ref : ∀ {n x A} {Γ : Ctx n} {Σ} →
        Γ , Σ ⊢ x ∶ A →
        ---------------------------------------
        Γ , Σ ⊢ ref x ∶ Ref A

  !_  : ∀ {n x A} {Γ : Ctx n} {Σ} →
        Γ , Σ ⊢ x ∶ Ref A →
        ---------------------------------------
        Γ , Σ ⊢ (! x) ∶ A

  _≔_ : ∀ {n i x A} {Γ : Ctx n} {Σ} →
        Γ , Σ ⊢ i ∶ Ref A →
        Γ , Σ ⊢ x ∶ A →
        ---------------------------------------
        Γ , Σ ⊢ (i ≔ x) ∶ Unit

open import Relation.Binary.List.Pointwise

-- store welltypedness relation
-- as a pointwise lifting of the welltyped relation on closed expressions between a world and a store
_,_⊢_ : ∀ {n} → Ctx n → World → Store n → Set
Γ , Σ ⊢ μ = Rel (λ A x → Γ , Σ ⊢ proj₁ x ∶ A) Σ μ
