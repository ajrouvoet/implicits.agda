module Examples.Resolution where

data TC : Set where

open import Prelude
open import Implicits.Calculus.WellTyped TC
open import Implicits.Calculus.Types.Constructors TC
open import Implicits.Calculus.Substitutions TC
open import Extensions.ListFirst
open Rules


free-nat = (tp-weaken (((tp-weaken tnat) ∙ (tvar zero))))

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
