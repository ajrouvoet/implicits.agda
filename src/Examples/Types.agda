module Examples.Types where

open import Prelude
open import Implicits.Calculus.WellTyped
open import Implicits.Calculus.Types.Constructors
open import Implicits.Calculus.Substitutions

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
