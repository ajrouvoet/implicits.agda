module Examples.Effects where

open import Prelude

open import Effects.Denotational
open import Effects.WellTyped EC _ec≟_
open import Effects.Substitutions EC _ec≟_
open import Implicits.Calculus.Types

-- value abstraction
module ex₁ where

  f : Term 0 0 0
  f = λ' unit print

  -- a lazy print is pure, but has a latent effect IO
  ⊢f : [] ⊢ f ∈ unit →[ List.[ has io ] ] unit & pure 
  ⊢f = λ' unit (does io)

  -- when we apply the above term
  -- the latent effect pops up
  f·t : Term 0 0 0
  f·t = f · tt

  ⊢f·t : [] ⊢ f·t ∈ unit & List.[ (has io) ]
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
    & pure
  wt-f = H (Λ (Λ (λ' (tvar zero →[ evar zero & pure ] tvar (suc zero))
    (λ' (tvar zero) (var (suc zero) · var zero)))))

module ex₃ where
  eff : Effects 0
  eff = (has io) & (has read) & pure

  -- lists of effects transtlate to tuples of Can*
  test : ⟦ eff , ([] , []) ⟧ef ≡ C.rec (tc CanIO ∷ tc CanRead ∷ [])
  test = refl
