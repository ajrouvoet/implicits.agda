module SystemF.BigStep.Extrinsic.Terms where

open import Prelude
open import SystemF.BigStep.Types
open import Data.List
open import Data.Fin.Substitution

-- erased (type-free) System F syntax
data Term : Set where
  unit : Term
  ƛ : Term → Term
  Λ : Term → Term
  _·_ : Term → Term → Term
  _[-] : Term → Term
  var : ℕ → Term
