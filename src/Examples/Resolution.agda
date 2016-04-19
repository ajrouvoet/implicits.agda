module Examples.Resolution where

open import Prelude
open import Implicits.Syntax
open import Implicits.Syntax.Type.Constructors
open import Implicits.WellTyped
open import Implicits.Substitutions
open import Extensions.ListFirst
open Rules

unit = 0

-- simple implicit resolution by implication
module ex₁ where
  r : Type zero
  r = ∀' (tp-weaken tnat ⇒ (TVar zero))

  -- proof that the above type is a rule
  r-isrule : IsRule r
  r-isrule = ∀'-rule (rule (tp-weaken tnat) (TVar zero))

  -- the context used
  K = tnat ∷K nil

-- partial implicit resolution
-- as described by Oliveira et al
module ex₂ where
  r : Type zero
  r = (tnat ⇒ TC unit ⇒ TC unit)

  -- proof that the above type is a rule
  r-isrule : IsRule r
  r-isrule = rule tnat (TC unit ⇒ TC unit)

  K : Ktx 0 1
  K = TC unit ∷K nil

-- higher order resolution
module ex₃ where
  r : Type zero
  r = ∀' ((TC unit ⇒ TVar zero) ⇒ (TVar zero ×' TVar zero))

  r' : Type zero
  r' = (TC unit ⇒ tnat) ⇒ (tnat ×' tnat)

  r-isrule : IsRule r
  r-isrule = ∀'-rule (rule (TC unit ⇒ TVar zero) (TVar zero ×' TVar zero))

  r'-isrule : IsRule r'
  r'-isrule = rule (TC unit ⇒ tnat) (tnat ×' tnat)

  K : Ktx 0 1
  K = (TC unit ⇒ tnat) ∷K nil

