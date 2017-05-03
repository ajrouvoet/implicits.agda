open import Prelude

open import Data.Nat
open import Data.Nat.Properties
open import Induction.Nat

module Implicits.Resolution.GenericFinite.Examples.MaximumDepth
  where

open import Implicits.Resolution.GenericFinite.TerminationCondition

_<′?_ : (x y : ℕ) → Dec (x <′ y)
x <′? y with (suc x) ≤? y
x <′? y | yes p = yes (≤⇒≤′ p)
x <′? y | no ¬p = no (λ p → ¬p (≤′⇒≤ p))

MaxDepthCondition : TerminationCondition
MaxDepthCondition = record
  {  TCtx = ℕ
  ; _<_  = _<′_
  ; _<?_  = _<′?_
  ; step = λ n _ _ _ _ → n ∸ 1
  ; wf-< = <-well-founded
  }
