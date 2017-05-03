open import Prelude

module Implicits.Resolution.Termination.SizeMeasures where

open import Induction.WellFounded
open import Induction.Nat
open import Data.Product hiding (map)
open import Data.Nat.Base using (_<′_)
open import Data.Fin hiding (_+_; _≤_; _<_; _≤?_)
open import Data.List hiding (map)
open import Data.List.All
open import Implicits.Syntax
open import Implicits.Syntax.Type.Unification
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties

-- a strict sizemeasure for types
||_|| : ∀ {ν} → Type ν → ℕ
|| simpl (tc x) || = 1
|| simpl (tvar n) || = 1
|| simpl (a →' b) || = 1 + || a || + || b ||
|| a ⇒ b || = 1 + || a || + || b ||
|| ∀' a || = 1 + || a ||

-- size of the head of a type
h||_|| : ∀ {ν} → Type ν → ℕ
h|| a || = || proj₂ (a ◁) ||

-- type measure on metatypes
m||_|| : ∀ {m ν} → MetaType m ν → ℕ
m|| simpl (tc x) || = 1
m|| simpl (tvar n) || = 1
m|| simpl (mvar n) || = 1
m|| simpl (a →' b) || = suc (m|| a || + m|| b ||)
m|| a ⇒ b || = 1 + (m|| a || + m|| b ||)
m|| ∀' a || = 1 + m|| a ||

-- We package Type with it's deBruijn counter because
-- we need to express orderings such as a sρ< ∀' a
-- where the number of free variables varies.
-- We could express that as ∀ {ν μ} → Type ν → Type μ → Set,
-- but Well-founded _sρ<_ unifies ν and μ,
-- such that the well-founded proof would be too narrow
_hρ≤_ : (a b : ∃ Type) → Set
(_ , a) hρ≤ (_ , b) = h|| a || ≤ h|| b ||

_hρ<_ : (a b : ∃ Type) → Set
(_ , a) hρ< (_ , b) = h|| a || < h|| b ||

_hρ<?_ : ∀ {ν μ} → (a : Type ν) → (b : Type μ) → Dec ((ν , a) hρ< (μ , b))
a hρ<? b with h|| a || | h|| b ||
a hρ<? b | y | z = (suc y) ≤? z

_ρ<_ : ∃ Type → ∃ Type → Set
(_ , a) ρ< (_ , b) = || a || < || b ||

_ρ<?_ : (a b : ∃ Type) → Dec (a ρ< b)
(_ , a) ρ<? (_ , b) with || a || | || b ||
(_ , a) ρ<? (_ , b) | y | z = (suc y) ≤? z

_m<_ : ∃₂ MetaType → ∃₂ MetaType → Set
(_ , _ , a) m< (_ , _ , b) = m|| a || < m|| b ||

_occ[_]<_ : ∀ {ν μ} (a : Type ν) (x : ℕ) (b : Type μ) → Set
a occ[ x ]< b = (occ x (proj₂ (a ◁))) ≤ (occ x (proj₂ (b ◁)))

-- oliveira's termination condition on types
data ⊢term {ν} : (Type ν) → Set where
  term-simp : ∀ {τ} → ⊢term (simpl τ)
  term-tabs : ∀ {a} → ⊢term a → ⊢term (∀' a)
  term-iabs : ∀ {a b} → ⊢term a → ⊢term b → (, a) hρ< (, b) →
              All (λ x → a occ[ toℕ x ]< b) (fvars a ++ fvars b) →
              ⊢term (a ⇒ b)
