open import Prelude

module Implicits.Improved.Finite.Termination (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Improved.Finite.Termination.SizeMeasures TC _tc≟_ public
open import Implicits.Improved.Finite.Termination.Lemmas TC _tc≟_ public
