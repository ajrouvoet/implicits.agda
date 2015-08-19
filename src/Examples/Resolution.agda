module Examples.Resolution where

data TC : Set where
  unit : TC

open import Prelude
open import Implicits.Calculus.WellTyped TC
open import Implicits.Calculus.Types.Constructors TC
open import Implicits.Calculus.Substitutions TC
open import Extensions.ListFirst
open Rules

-- simple implicit resolution by implication
module ex₁ where
  r : Type zero
  r = ∀' (tp-weaken tnat ⇒ (tvar zero))

  -- proof that the above type is a rule
  r-isrule : IsRule r
  r-isrule = ∀'-rule (rule (tp-weaken tnat) (tvar zero))

  -- the subsumption of the domain by tnat
  eq : tnat ⊑ (∀' $ tp-weaken tnat)
  eq = poly-intro (poly-equal refl)

  -- the context used
  K = tnat ∷K nil

  -- the implicit derivation of the codomain from the domain, using the implicit rule
  ex₁ : ρ⟨ K , r ⟩↝ (∀' (tvar zero))
  ex₁ = by-implication
    (by-value r) -- the rule used
    r-isrule     -- proof that r is an implication
    (, First.here (by-subsumption (by-value tnat) eq) List.[]) -- the domain is derivable

-- partial implicit resolution
-- as described by Oliveira et al
module ex₂ where
  r : Type zero
  r = (tnat ⇒ tc unit ⇒ tc unit)

  -- proof that the above type is a rule
  r-isrule : IsRule r
  r-isrule = rule tnat (tc unit ⇒ tc unit)

  K : Ktx 0 1
  K = tc unit ∷K nil

  test : ρ⟨ K , r ⟩↝ (tnat ⇒ tc unit)
  test = by-composition r-isrule p
    where
      p : ρ⟨ tnat ∷K K , tc unit ⇒ tc unit ⟩↝ (tc unit)
      p = (by-implication (by-value (tc unit ⇒ tc unit)) (rule (tc unit) (tc unit))
        (, there tnat (here (by-value (tc unit)) List.[])))

-- higher order resolution
module ex₃ where
  r : Type zero
  r = ∀' ((tc unit ⇒ tvar zero) ⇒ (tvar zero ×' tvar zero))

  r' : Type zero
  r' = (tc unit ⇒ tnat) ⇒ (tnat ×' tnat)

  r-isrule : IsRule r
  r-isrule = ∀'-rule (rule (tc unit ⇒ tvar zero) (tvar zero ×' tvar zero))

  r'-isrule : IsRule r'
  r'-isrule = rule (tc unit ⇒ tnat) (tnat ×' tnat)

  K : Ktx 0 1
  K = (tc unit ⇒ tnat) ∷K nil

  -- the subsumption proof
  sub : ∀' ((tc unit ⇒ tvar zero) ⇒ (tvar zero ×' tvar zero)) ⊑ (tc unit ⇒ tnat) ⇒ (tnat ×' tnat)
  sub = poly-elim tnat (poly-equal refl)

  -- we have trouble here, because the subsumption goes only on the result
  -- it does not transform the domain of an implication
  test : ρ⟨ K , r ⟩↝ (tnat ×' tnat)
  test = by-implication
    (by-subsumption (by-value r) sub)
    r'-isrule
    (, here (by-value (tc unit ⇒ tnat)) List.[])

