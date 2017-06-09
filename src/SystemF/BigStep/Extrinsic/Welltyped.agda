module SystemF.BigStep.Extrinsic.Welltyped where

open import Prelude
open import SystemF.BigStep.Types
open import SystemF.BigStep.Extrinsic.Terms
open import Data.List hiding ([_])
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

open import Relation.Binary.List.Pointwise hiding (refl; map) public

-- welltypedness relations between typing contexts and environmets
-- is just the pointwise extension of value-welltypedness
_⊢_ : ∀ {n} → Ctx n → Env → Set

data ⊢̬_∶_ {n} : Val → Type n → Set where

  unit : -------------------
        ⊢̬ unit ∶ Unit

  clos : ∀ {b t}{Γ : Ctx n}{E a} →
          (a ∷ Γ) ⊢ t ∶ b →
          Γ ⊢ E →
          -------------------
          ⊢̬ clos E t ∶ (a ⇒ b)

  tclos : ∀ {a t}{Γ : Ctx n}{E} →
          (Γ ctx/ wk) ⊢ t ∶ a →
          Γ ⊢ E →
          ---------------------
          ⊢̬ tclos E t ∶ ∀' a

Γ ⊢ E = Rel (λ{ a v → ⊢̬ v ∶ a}) Γ E

open import Data.Fin.Substitution

_wt/_ : ∀ {n m}{Γ : Ctx n}{t a} → Γ ⊢ t ∶ a → (ρ : Sub Type n m) → (Γ ctx/ ρ) ⊢ t ∶ (a / ρ)
unit wt/ ρ = unit
ƛ a t wt/ ρ = ƛ (a / ρ) (t wt/ ρ)
var x wt/ ρ = var ([]=-map x)
(f · e) wt/ ρ = (f wt/ ρ) · (e wt/ ρ)
Λ t wt/ ρ = Λ (subst (λ Γ → Γ ⊢ _ ∶ _) (sym $ CtxLemmas.ctx/-wk-comm _ ρ) (t wt/ (ρ ↑)))
(_[_] {a = a} t b) wt/ ρ =
  subst (λ a → _ ⊢ _ ∶ a) (sym $ Lemmas.sub-commutes a) ((t wt/ ρ) [ (b / ρ) ])
