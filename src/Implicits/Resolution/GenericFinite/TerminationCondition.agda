open import Prelude

module Implicits.Resolution.GenericFinite.TerminationCondition 
  where

open import Induction.WellFounded
open import Implicits.Syntax

record TerminationCondition : Set₁ where
  field
    TCtx : Set
    _<_  : TCtx → TCtx → Set
    _<?_  : (x y : TCtx) → Dec (x < y)
    step : ∀ {ν} → TCtx → ICtx ν → Type ν → Type ν → SimpleType ν → TCtx
    wf-< : Well-founded _<_

  T-Acc : TCtx → Set
  T-Acc Φ = Acc _<_ Φ
