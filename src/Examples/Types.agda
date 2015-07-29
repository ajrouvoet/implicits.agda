module Examples.Types where

data TC : Set where

open import Prelude
open import Implicits.Calculus.WellTyped TC
open import Implicits.Calculus.Types.Constructors TC
open import Implicits.Calculus.Substitutions TC

nattid = (∀' (
  ((tp-weaken tnat) ∙ (tvar zero))
  →'
  ((tp-weaken tnat) ∙ (tvar zero))))

tnat⊑tnat : tnat ⊑ tnat
tnat⊑tnat = poly-equal refl

tid⊑nattid : tid ⊑ nattid
tid⊑nattid = poly-intro ((poly-elim (tp-weaken tnat ∙ tvar zero)) (poly-equal refl))

-- ∀S.∀T.S → T ⊑ ∀T.T → tnat
test4 : (∀' (∀' (tvar (suc zero) →' tvar zero))) ⊑
          ∀' (∀' ((tvar (suc zero)) →' (tp-weaken $ (tp-weaken tnat) ∙ (tvar zero))))
test4 = poly-intro (
  poly-elim (tvar zero)
    (poly-elim ((tp-weaken tnat) ∙ (tvar zero))
      (poly-intro
        (poly-equal refl)
      )
    )
  )
