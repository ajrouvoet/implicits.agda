module Implicits.SystemF.Terms.Constructors where

open import Prelude
open import Implicits.SystemF.WellTyped
open import Implicits.SystemF.Substitutions.Lemmas
open import Implicits.SystemF.Types.Constructors

open Functions

-- polymorphic function application
-- applies a polymorphic function to an argument with the type of the domain
poly-· : ∀ {ν n} {a : Type ν} {K : Ctx ν n} {f arg} →
         (fa : IsFunction a) → K ⊢ f ∈ a → K ⊢ arg ∈ domain fa → ∃ λ t → K ⊢ t ∈ codomain fa
poly-· (lambda a b) ⊢f ⊢arg = , ⊢f · ⊢arg
poly-· {K = K} {f = f} {arg = arg} (∀'-lambda {a} fa) ⊢f ⊢arg = , Λ (proj₂ (poly-· fa f' arg'))
  where
    f' : ctx-weaken K ⊢ _ ∈ a
    f' = subst
      (λ τ → ctx-weaken K ⊢ _ ∈ τ)
     (TypeLemmas.a-/Var-varwk↑-/-sub0≡a a)
      ((⊢tp-weaken ⊢f) [ tvar zero ])
    arg' : ctx-weaken K ⊢ (tm-weaken arg) [ tvar zero ] ∈ domain fa
    arg' = subst
      (λ τ → ctx-weaken K ⊢ _ ∈ τ)
      (TypeLemmas.a-/Var-varwk↑-/-sub0≡a (domain fa))
      ((⊢tp-weaken ⊢arg) [ tvar zero ])
