open import Prelude

module Implicits.Resolution.Termination.Lemmas
  where

open import Induction.WellFounded
open import Induction.Nat
open import Data.Fin.Substitution
open import Implicits.Syntax
open import Implicits.Syntax.Type.Unification
open import Implicits.Substitutions
open import Implicits.Substitutions.Lemmas
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
open import Relation.Binary using (module DecTotalOrder)
open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl)
open import Extensions.Nat

open import Implicits.Resolution.Termination.Lemmas.SizeMeasures public
-- open import Implicits.Resolution.Termination.Lemmas.Stack public
