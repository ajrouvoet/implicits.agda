module Examples.Effects where

open import Prelude

open import Effects.Denotational
open import Effects.WellTyped EC _ec≟_
open import Effects.Substitutions EC _ec≟_
open import Implicits.Calculus.Types

-- value abstraction
module ex₁ where

  f : Term 0 0 0
  f = λ' unit (does io)

  -- a lazy print is pure, but has a latent effect IO
  ⊢f : [] ⊢ f ∈ unit →[ has io & pure ] unit + pure 
  ⊢f = λ' unit (does io)

  -- when we apply the above term
  -- the latent effect pops up
  f·t : Term 0 0 0
  f·t = f · tt

  ⊢f·t : [] ⊢ f·t ∈ unit + has io & pure
  ⊢f·t = ⊢f · tt

-- effect abstraction
module ex₂ where
  f : Term 0 0 0
  f = H (Λ (Λ (
    λ'
      (tvar zero →[ evar zero & pure ] tvar (suc zero))
      (λ' (tvar zero) ((var (suc zero)) · (var zero)))
    )))

  wt-f : [] ⊢ f ∈
    H (∀' (∀' ((
      tvar zero →[ evar zero & pure ] tvar (suc zero)) →[ pure ]
      (tvar zero →[ evar zero & pure ] (tvar (suc zero)))
    )))
    + pure
  wt-f = H (Λ (Λ (λ' (tvar zero →[ evar zero & pure ] tvar (suc zero))
    (λ' (tvar zero) (var (suc zero) · var zero)))))

module ex₃ where
  eff : Effects 0
  eff = (has io) & (has read) & pure

  -- lists of effects transtlate to tuples of Can*
  test : ⟦ eff , ([] , []) ⟧efs ≡ C.rec (tc CanIO ∷ tc CanRead ∷ [])
  test = refl

module ex₄ where
  f : Term 0 0 0
  f = Λ (λ' unit (does io))

  wt-f : [] ⊢ f ∈ (∀' (unit →[ has io & pure ] unit)) + pure
  wt-f = Λ (λ' unit (does io))

  test : ⟦ wt-f , ([] , []) ⟧ ≡
    C.Λ (C.λ' (tc unit) ((C.ρ (tc CanIO) ((C.ρ (tc CanIO) (C.new unit)) C.⟨⟩))))
  test = refl

module ex₅ where
  open ex₄

  tapp : Term 0 0 0
  tapp = f [ unit ]

  wt-tapp : [] ⊢ tapp ∈ (unit →[ has io & pure ] unit) + pure
  wt-tapp = wt-f [ unit ]

  app : Term 0 0 0
  app = tapp · tt

  wt-app : [] ⊢ app ∈ unit + has io & pure
  wt-app = wt-tapp · tt
