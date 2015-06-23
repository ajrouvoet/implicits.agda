module Implicits.SystemF.Terms.Constructors where

open import Prelude
open import Data.Fin.Substitution
open import Implicits.SystemF.Types
open import Implicits.SystemF.Terms
open import Implicits.SystemF.WellTyped
open import Implicits.SystemF.Substitutions.Lemmas
open import Implicits.SystemF.Substitutions as S using ()
open import Implicits.SystemF.Types.Constructors

open TypeLemmas hiding (subst)

postulate ∀'-weaken-wt : ∀ {ν n} {Γ : Ctx ν n} {a t b} →
                         (∀' a) ∷ Γ ⊢ t ∈ b → a ∷ (ctx-weaken Γ) ⊢ tm-weaken t ∈ tp-weaken b

-- building a ml-normalized lambda term:
-- i.e. build an abstraction whose type is a ml-style, weakly polomorphic, type
-- with all quantifiers at the top
-- well founded on number of universal quantifiers
{-# NO_TERMINATION_CHECK #-}
⊢λml : ∀ {ν n} {Γ : Ctx ν n} {b t} a → (⊢b : a ∷ Γ ⊢ t ∈ b) →
                 ∃ λ t' → Γ ⊢ t' ∈ (a →ml b)
⊢λml {b = tvar n} (tvar x) ⊢t = , λ' (tvar x) ⊢t
⊢λml {b = a →' b} (tvar x) ⊢t = , λ' (tvar x) ⊢t
⊢λml {Γ = Γ} {b = ∀' b} {t = t} (tvar x) ⊢t = , Λ (proj₂ $ ⊢λml (tp-weaken (tvar x)) u)
  where 
    -- first we weaken ⊢t and proof it still has a polymorphic shape
    wt-∀ : tp-weaken (tvar x) ∷ ctx-weaken Γ ⊢ tm-weaken t ∈ ∀' (b tp/tp wk ↑)
    wt-∀ = subst₂
      (λ i j → i ∷ ctx-weaken Γ ⊢ tm-weaken t ∈ j)
      (/-wk {t = tvar x}) (sym $ /-wk {t = ∀' b})
      (WtTypeLemmas.weaken ⊢t)
    -- then we apply it and proof that it then has type b again
    u : tp-weaken (tvar x) ∷ ctx-weaken Γ ⊢ (tm-weaken t) [ tvar zero ] ∈ b
    u = subst
      (λ u → tp-weaken (tvar x) ∷ ctx-weaken Γ ⊢ (tm-weaken t) [ tvar zero ] ∈ u)
      (a/wk↑/sub0≡a b)
      (wt-∀ [ tvar zero ])
⊢λml {b = tvar n₁} (a →' c) ⊢t = , λ' (a →' c) ⊢t
⊢λml {b = b →' b₁} (a →' c) ⊢t = , λ' (a →' c) ⊢t
⊢λml {Γ = Γ} {b = ∀' b} {t = t} (a →' c) ⊢t =  , Λ (proj₂ $ ⊢λml (tp-weaken (a →' c)) u)
  where 
    -- first we weaken ⊢t and proof it still has a polymorphic shape
    wt-∀ : tp-weaken (a →' c) ∷ ctx-weaken Γ ⊢ tm-weaken t ∈ ∀' (b tp/tp wk ↑)
    wt-∀ = subst₂
      (λ i j → i ∷ ctx-weaken Γ ⊢ tm-weaken t ∈ j)
      (/-wk {t = a →' c}) (sym $ /-wk {t = ∀' b})
      (WtTypeLemmas.weaken ⊢t)
    -- then we apply it and proof that it then has type b again
    u : tp-weaken (a →' c) ∷ ctx-weaken Γ ⊢ (tm-weaken t) [ tvar zero ] ∈ b
    u = subst
      (λ u → tp-weaken (a →' c) ∷ ctx-weaken Γ ⊢ (tm-weaken t) [ tvar zero ] ∈ u)
      (a/wk↑/sub0≡a b)
      (wt-∀ [ tvar zero ])
⊢λml (∀' a) ⊢t with (⊢λml a (∀'-weaken-wt ⊢t))
⊢λml (∀' a) ⊢t | _ , ih = , Λ ih
