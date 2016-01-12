open import Prelude

module Implicits.Resolution.Termination.Lemmas
  (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Induction.WellFounded
open import Induction.Nat
open import Data.Fin.Substitution
open import Implicits.Syntax TC _tc≟_
open import Implicits.Syntax.Type.Unification TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open import Implicits.Substitutions.Lemmas TC _tc≟_
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
open import Relation.Binary using (module DecTotalOrder)
open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl)
open import Extensions.Nat

open import Implicits.Resolution.Termination.Lemmas.SizeMeasures TC _tc≟_ public
-- open import Implicits.Resolution.Termination.Lemmas.Stack TC _tc≟_ public
