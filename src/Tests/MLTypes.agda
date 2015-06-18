module Tests.MLTypes where

open import Prelude
open import Implicits.Calculus.WellTyped
open import Implicits.Calculus.Types.Constructors
open import Implicits.Calculus.Terms.Constructors
open import Implicits.Calculus.Substitutions

nattid = (tnat →ₚ tnat)

tnat⊑tnat : tnat ⊑ tnat
tnat⊑tnat = poly-forall (mono refl)

tid⊑nattid : tid ⊑ nattid
tid⊑nattid = poly-instance tnat (poly-forall (mono refl))

open import Data.Fin.Substitution
open TypeSubst
open TermSubst typeSubst

test4 : (∀' (∀' (mono (tvar (suc zero) →' tvar zero)))) ⊑ 
            ∀' ((mono (tvar zero)) →ₚ (pt-weaken tnat))
test4 = poly-forall (poly-instance (pt-weaken tnat) (poly-forall (mono refl)))

test4' : (∀' (∀' (mono (tvar (suc zero) →' tvar zero)))) ⊑ 
            ∀' ((pt-weaken tnat) →ₚ (mono (tvar zero)))
test4' = poly-instance tnat (poly-forall (poly-forall (mono refl)))
