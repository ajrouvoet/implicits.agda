module Examples.Resolution where

open import Prelude
open import Implicits.Calculus.WellTyped
open import Implicits.Calculus.Types.Constructors
open import Implicits.Calculus.Substitutions
open import Extensions.ListFirst
open Rules


free-nat = (tp-weaken (mono-totype $ ((pt-weaken tnat) ∙ (tvar zero))))

r : PolyType zero
r =
  ∀' (
    ∀' (
      mono (
        free-nat
        ⇒
        (tvar $ suc (zero))
      )
    )
  )

-- proof that the above type is a rule
r-isrule : IsRule r
r-isrule = ∀'-rule (∀'-rule (rule free-nat (tvar (suc zero))))

-- the subsumption of the domain by tnat
eq : tnat ⊑ ∀' (∀' (mono free-nat))
eq = poly-intro (poly-elim (tvar zero) (poly-intro (poly-equal refl)))

-- the context used
K = tnat ∷K nil

-- the implicit derivation of the codomain from the domain, using the implicit rule
ex₁ : ρ⟨ K , r ⟩↝ ∀' (∀' (mono (tvar (suc zero))))
ex₁ = by-implication
  (by-value r) -- the rule used
  r-isrule     -- proof that r is an implication
  (, First.here (by-subsumption (by-value tnat) eq) List.[]) -- the domain is derivable
