module SystemF.BigStep.Extrinsic.Welltyped where

open import Prelude
open import SystemF.BigStep.Types
open import SystemF.BigStep.Extrinsic.Terms
open import Data.List
open import Extensions.List

-- welltyped terms
data _⊢_∶_ {n}(Γ : Ctx n) : Term → Type n → Set where

  unit : -------------------
         Γ ⊢ unit ∶ Unit

  ƛ : ∀ {b t} a →
      (a ∷ Γ) ⊢ t ∶ b →
      -------------------
      Γ ⊢ ƛ t ∶ (a ⇒ b)

  var : ∀ {a i} →
      Γ [ i ]= a →
      -------------
      Γ ⊢ var i ∶ a

  _·_ : ∀ {f e a b} →
      Γ ⊢ f ∶ (a ⇒ b) →
      Γ ⊢ e ∶ a →
      ---------------
      Γ ⊢ f · e ∶ b

  Λ : ∀ {a t} →
      (Γ ctx/ wk) ⊢ t ∶ a →
      ---------------------
      Γ ⊢ Λ t ∶ ∀' a

  _[_] : ∀ {f a} →
      Γ ⊢ f ∶ (∀' a) →
      (b : Type n) →
      ---------------------------
      Γ ⊢ f [-] ∶ (a / (sub b))
