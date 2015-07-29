module Examples.Effects where

open import Prelude

-- the effect primitives
data EC : Set where
  read : EC
  write : EC
  throw : EC
  io : EC

_ec≟_ : Decidable {A = EC} _≡_
read ec≟ read = yes refl
read ec≟ write = no (λ ())
read ec≟ throw = no (λ ())
read ec≟ io = no (λ ())
write ec≟ read = no (λ ())
write ec≟ write = yes refl
write ec≟ throw = no (λ ())
write ec≟ io = no (λ ())
throw ec≟ read = no (λ ())
throw ec≟ write = no (λ ())
throw ec≟ throw = yes refl
throw ec≟ io = no (λ ())
io ec≟ read = no (λ ())
io ec≟ write = no (λ ())
io ec≟ throw = no (λ ())
io ec≟ io = yes refl

open import Effects.WellTyped EC _ec≟_
open import Effects.Substitutions EC _ec≟_

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
