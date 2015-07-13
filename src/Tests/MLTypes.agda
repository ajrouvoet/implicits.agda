module Tests.MLTypes where

open import Prelude
open import Implicits.Calculus.WellTyped
open import Implicits.Calculus.Types.Constructors
open import Implicits.Calculus.Substitutions

nattid = (∀' (mono (
  (mono-totype ((pt-weaken tnat) ∙ (tvar zero)))
  →'
  (mono-totype ((pt-weaken tnat) ∙ (tvar zero))))))

tnat⊑tnat : tnat ⊑ tnat
tnat⊑tnat = poly-equal refl

tid⊑nattid : tid ⊑ nattid
tid⊑nattid = poly-intro (poly-elim (mono-totype (pt-weaken tnat ∙ tvar zero)) (poly-equal refl))

-- ∀S.∀T.S → T ⊑ ∀T.T → tnat
test4 : (∀' (∀' (mono (tvar (suc zero) →' tvar zero)))) ⊑ 
          ∀' (∀' (mono (
            (tvar (suc zero))
            →'
            (tp-weaken $ mono-totype ((pt-weaken tnat) ∙ (tvar zero)))
        )))
test4 = poly-intro (
  poly-elim (tvar zero)
    (poly-elim (mono-totype ((pt-weaken tnat) ∙ (tvar zero)))
      (poly-intro
        (poly-equal refl)
      )
    )
  )
