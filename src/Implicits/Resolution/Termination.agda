open import Prelude

module Implicits.Resolution.Termination (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Resolution.Termination.SizeMeasures TC _tc≟_ public
open import Implicits.Resolution.Termination.Stack TC _tc≟_ public
open import Implicits.Resolution.Termination.Lemmas TC _tc≟_ public
