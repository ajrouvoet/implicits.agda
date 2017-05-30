module FSub.Intrinsic.Algorithmic.Syntax where

-- Welltyped syntax for Kernel F<: (Chap. 26/28 of TAPL)
-- We're using an algorithmic definition of subtyping.
-- This means that there is no special for subsumption and
-- subtyping derivations are unique.
-- It also means we don't have <:-refl and <:-trans axioms.

open import Prelude
open import Data.Vec hiding (_>>=_)
open import Extensions.Vec

open import FSub.Types
open import FSub.Types.Subtyping
open Algorithmic public

-- intrinsically typed syntax for FSub without junk terms
data Term {n}(N : νCtx n)(Γ : Ctx n) : Type n → Set where
  unit : Term N Γ Unit
  ƛ : ∀ {b} (a : Type n) → Term N (Γ +tm a) b → Term N Γ (a ⇒ b)
  Λ : ∀ {a} u → Term (N +ν u) (Γ +ty) a → Term N Γ (∀≤ u a)
  _·[_,_]_ : ∀ {a a₁ a₂ b} → Term N Γ a →
              N ⊢ a ⇑ (a₁ ⇒ b) → N ⊢ a₂ <: a₁ →
              Term N Γ a₂ →
              Term N Γ b
  _[_,_] : ∀ {a a' b u} → Term N Γ a →
           N ⊢ a ⇑ (∀≤ u a') → N ⊢ b <: u →
           Term N Γ (a' / sub b)
  var : ∀ {a} → Var Γ a → Term N Γ a

open import Extensions.List
open import Data.List.Any.Membership
open import Data.List.Any
module Mem = Membership-≡
open import Function.Inverse
open import Function.Equality

postulate
  weaken-<: : ∀ {n N}{b : Type n}{bᵘ} u → N ⊢ b <: bᵘ → (N +ν u) ⊢ (b / wk) <: (bᵘ / wk)
  Γ-lem : ∀ {n bᵘ b}{Γ : Ctx n}(p : bᵘ Mem.∈ Γ) →
          ((Γ +ty) [ (Inverse.to map-∈↔ ⟨$⟩ (, (p , refl))) ]≔' (b / wk)) ≡ ((Γ [ p ]≔' b) +ty)
  narrow : ∀ {n N}{Γ : Ctx n}{a bᵘ b} → (p : bᵘ Mem.∈ Γ) → N ⊢ b <: bᵘ → Term N Γ a →
            ∃ λ a' → Term N (Γ [ p ]≔' b) a' × N ⊢ a' <: a
{-}
narrow p q unit = , unit , <:-refl
narrow p q (ƛ a t) with narrow (there p) q t
... | (b' , t' , sub) = (a ⇒ b'), ƛ a t' , <:-refl ⇒ sub
narrow p q (Λ u t) with narrow (Inverse.to map-∈↔ ⟨$⟩ (, (p , refl))) (weaken-<: u q) t
narrow p q (Λ u t) | a , t' , sub = (∀≤ u a) , (Λ u (subst (λ Γ → Term _ Γ _) (Γ-lem p) t') , ∀≤ sub)
narrow p q (f ·[ r , z ] e) = {!!} 
narrow p q (t [ x , x₁ ]) = {!!}
narrow p q (var x) with narrow-var x p q
  where
    narrow-var : ∀ {n N Γ}{a b bᵘ : Type n} → a Mem.∈ Γ → (p : bᵘ Mem.∈ Γ) → N ⊢ b <: bᵘ →
                 ∃ λ a' → a' Mem.∈ (Γ [ p ]≔' b) × N ⊢ a' <: a
    narrow-var {b = b} (here refl) (here refl) z = b , here refl , z
    narrow-var {a = a} (there p) (here px) z = a , (there p , <:-refl)
    narrow-var (here px) (there _) z = , here px , <:-refl
    narrow-var (there px) (there qx) z with narrow-var px qx z
    ... | a' , p , q = a' , there p , q
... | a' , x' , sub = a' , var x' , sub
-}
