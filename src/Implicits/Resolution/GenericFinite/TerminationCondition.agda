module Implicits.Resolution.GenericFinite.TerminationCondition where

open import Prelude
open import Induction.WellFounded

record TerminationCondition : Set₁ where
  field
    TCtx : Set
    _<_  : TCtx → TCtx → Set
    _<?_  : (x y : TCtx) → Dec (x < y)
    step : TCtx → TCtx
    wf-< : Well-founded _<_

  T-Acc : TCtx → Set
  T-Acc Φ = Acc _<_ Φ
