module FSub.Extrinsic.Declarative.Welltyped where

open import Prelude
open import Data.List
open import Extensions.List

open import FSub.Types
open import FSub.Types.Subtyping

open Declarative public
open import FSub.Extrinsic.Declarative.Syntax public

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

open import Relation.Binary.List.Pointwise hiding (refl; map) public

-- welltypedness relations between typing contexts and environmets
-- is just the pointwise extension of value-welltypedness
_,_⊢_ : ∀ {n} → νCtx n → Ctx n → Env → Set

data _⊢̬_∶_ {n}(N : νCtx n) : Val → Type n → Set where

  -- NOTE we have chosen *not* to include subsumption in the static semantics
  -- of values in exchange for canonical values;
  -- This means we only have minimal typings for values and we'll often
  -- have to work with the weaker judgement below

  unit : -------------------
         N ⊢̬ unit ∶ Unit

  clos : ∀ {b t}{Γ : Ctx n}{E a} →
          N , (a ∷ Γ) ⊢ t ∶ b →
          N , Γ ⊢ E →
          -------------------
          N ⊢̬ clos E t ∶ (a ⇒ b)

  tclos : ∀ {a t}{Γ : Ctx n}{E} u →
          N , Γ ⊢ E →
          (N +ν u) , (Γ ctx/ wk) ⊢ t ∶ a →
          ---------------------
          N ⊢̬ tclos E t ∶ ∀≤ u a

data _⊢̬_<:_ {n}(N : νCtx n) : Val → Type n → Set where
  _%_ : ∀ {v l u} → N ⊢̬ v ∶ l → N ⊢ l <: u → N ⊢̬ v <: u

N , Γ ⊢ E = Rel (λ a v → N ⊢̬ v <: a) Γ E

eraseᵗᵐ : ∀ {n}{N : νCtx n}{Γ t a} → N , Γ ⊢ t ∶ a → Term
eraseᵗᵐ {t = t} _ = t

eraseᴱ : ∀ {n}{N : νCtx n}{Γ E} → N , Γ ⊢ E → Env
eraseᴱ {E = E} _ = E

module Canonical where

  open import Data.Star

  -- All values upperbounded by some function type, themselves have a function type;
  -- You might expect the lemma to state that the value *is* a closure; but for this you need
  -- heterogeneous equality and (consequently?) the lemma is annoying to prove.
  <:⇒ : ∀ {n N v}{a b x : Type n} → N ⊢̬ v ∶ x → N ⊢ x <: a ⇒ b → ∃₂ λ a' b' → x ≡ (a' ⇒ b')
  <:⇒ v ε = _ , _ , refl
  <:⇒ () (ν x ◅ p)
  <:⇒ () (Bot<: ◅ _)
  <:⇒ v (_<:Top ◅ p) = ⊥-elim (<:-Lemmas.top-max (λ ()) p)
  <:⇒ v (∀≤ u ◅ p) = ⊥-elim (<:-Lemmas.¬∀≤⇒ p)
  <:⇒ v ((a ⇒ b) ◅ p) = _ , _ , refl

  -- Similar lemma for type closures
  <:∀≤ : ∀ {n N u a v}{x : Type n} → N ⊢̬ v ∶ x → N ⊢ x <: (∀≤ u a) → ∃₂ λ a' u' → x ≡ (∀≤ u' a')
  <:∀≤ v ε = _ , _ , refl
  <:∀≤ () (ν x ◅ p)
  <:∀≤ () (Bot<: ◅ p)
  <:∀≤ v (_<:Top ◅ p) = ⊥-elim (<:-Lemmas.top-max (λ ()) p)
  <:∀≤ v ((_ ⇒ _) ◅ p) = ⊥-elim (<:-Lemmas.¬⇒≤∀ p)
  <:∀≤ (tclos {a = a} u E t) (∀≤ x ◅ p) = a , u , refl
