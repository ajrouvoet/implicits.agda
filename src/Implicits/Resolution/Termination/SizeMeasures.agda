open import Prelude

module Implicits.Resolution.Termination.SizeMeasures (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Induction.WellFounded
open import Induction.Nat
open import Data.Nat.Base using (_<′_)
open import Implicits.Syntax TC _tc≟_
open import Implicits.Syntax.Type.Unification TC _tc≟_
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties

-- a strict sizemeasure for types
||_|| : ∀ {ν} → Type ν → ℕ
|| simpl (tc x) || = 1
|| simpl (tvar n) || = 1
|| simpl (a →' b) || = 1 N+ || a || N+ || b ||
|| a ⇒ b || = 1 N+ || a || N+ || b ||
|| ∀' a || = 1 N+ || a ||

-- size of the head of a type
h||_|| : ∀ {ν} → Type ν → ℕ
h|| a || = || proj₂ (a ◁) ||

-- type measure on metatypes
m||_|| : ∀ {m ν} → MetaType m ν → ℕ
m|| simpl (tc x) || = 1
m|| simpl (tvar n) || = 1
m|| simpl (mvar n) || = 1
m|| simpl (a →' b) || = suc (m|| a || N+ m|| b ||)
m|| a ⇒ b || = 1 N+ (m|| a || N+ m|| b ||)
m|| ∀' a || = 1 N+ m|| a ||

-- We package Type with it's deBruijn counter because
-- we need to express orderings such as a sρ< ∀' a
-- where the number of free variables varies.
-- We could express that as ∀ {ν μ} → Type ν → Type μ → Set,
-- but Well-founded _sρ<_ unifies ν and μ,
-- such that the well-founded proof would be too narrow
_hρ<_ : (a b : ∃ Type) → Set
(_ , a) hρ< (_ , b) = h|| a || N< h|| b ||

_hρ<?_ : ∀ {ν μ} → (a : Type ν) → (b : Type μ) → Dec ((ν , a) hρ< (μ , b))
a hρ<? b with h|| a || | h|| b ||
a hρ<? b | y | z = (suc y) N≤? z

_ρ<_ : ∃ Type → ∃ Type → Set
(_ , a) ρ< (_ , b) = || a || N< || b ||

_ρ<?_ : (a b : ∃ Type) → Dec (a ρ< b)
(_ , a) ρ<? (_ , b) with || a || | || b ||
(_ , a) ρ<? (_ , b) | y | z = (suc y) N≤? z

_m<_ : ∃₂ MetaType → ∃₂ MetaType → Set
(_ , _ , a) m< (_ , _ , b) = m|| a || N< m|| b ||
