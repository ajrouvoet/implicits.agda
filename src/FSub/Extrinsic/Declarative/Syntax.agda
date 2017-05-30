module FSub.Extrinsic.Declarative.Syntax where

open import Prelude
open import Data.List
open import Extensions.List

open import SystemF.BigStep.Extrinsic.Terms

open import FSub.Types
open import FSub.Types.Subtyping
open Declarative public

data _,_⊢_∶_ {n}(N : νCtx n)(Γ : Ctx n) : Term → Type n → Set where

  unit : -------------------
         N , Γ ⊢ unit ∶ Unit

  ƛ : ∀ {b t} a →
      N , (a ∷ Γ) ⊢ t ∶ b →
      -------------------
      N , Γ ⊢ ƛ t ∶ (a ⇒ b)

  var : ∀ {a i} →
      Γ [ i ]= a →
      -------------
      N , Γ ⊢ var i ∶ a

  _·_ : ∀ {f e a b} →
        N , Γ ⊢ f ∶ (a ⇒ b) →
        N , Γ ⊢ e ∶ a →
        ---------------
        N , Γ ⊢ f · e ∶ b

  Λ : ∀ {a t} u →
      (N +ν u) , (Γ ctx/ wk) ⊢ t ∶ a →
      ---------------------
      N , Γ ⊢ Λ t ∶ ∀≤ u a

  _[_] : ∀ {f u a b} →
         N , Γ ⊢ f ∶ (∀≤ u a) →
         N ⊢ b <: u →
         ---------------------------
         N , Γ ⊢ f [-] ∶ (a / (sub b))

  subm : ∀ {t a b} →
         N , Γ ⊢ t ∶ a →
         N ⊢ a <: b →
         ---------------
         N , Γ ⊢ t ∶ b
