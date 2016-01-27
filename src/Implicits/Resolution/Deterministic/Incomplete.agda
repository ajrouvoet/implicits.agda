open import Prelude hiding (id; Bool)

module Implicits.Resolution.Deterministic.Incomplete where

data TC : Set where
  tc-int : TC
  tc-bool : TC

_tc≟_ : (a b : TC) → Dec (a ≡ b)
tc-int tc≟ tc-int = yes refl
tc-int tc≟ tc-bool = no (λ ())
tc-bool tc≟ tc-int = no (λ ())
tc-bool tc≟ tc-bool = yes refl

open import Implicits.Syntax TC _tc≟_
open import Implicits.WellTyped TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open import Extensions.ListFirst

Bool : Type 0
Bool = simpl $ tc tc-bool

Int : Type 0
Int = simpl $ tc tc-int

-- We'll proof incompleteness with a simple example that we'll be able to resolve
-- using the ambigous resolution rules, but not with the deterministic rules.
-- This proofs that the ambiguous rules are stronger, such that together with Oliveira's
-- proof that determinstic resolution is sound w.r.t. ambiguous resolution, we have the
-- result that deterministic resolution is incomplete (or ambiguous resolution is strictly stronger)

Δ : ICtx 0
Δ = (Int ⇒ Bool) List.∷ Bool List.∷ List.[]

open import Implicits.Resolution.Deterministic.Resolution TC _tc≟_ as D
open import Implicits.Resolution.Ambiguous.Resolution TC _tc≟_ as A
open import Extensions.ListFirst

private
  -- proof that Bool is not derivable under the deterministic resolution rules
  deterministic-cant : ¬ (Δ D.⊢ᵣ Bool)
  deterministic-cant (r-simp fst fst↓bool) with
    FirstLemmas.first-unique (here (m-iabs m-simp) (Bool List.∷ List.[])) fst
  deterministic-cant (r-simp fst (i-iabs (r-simp r _) b)) | refl = ¬r◁Int (, r)
    where
      ¬r◁Int : ¬ (∃ λ r → Δ ⟨ tc tc-int ⟩= r)
      ¬r◁Int (._ , here (m-iabs ()) ._)
      ¬r◁Int (._ , there _ _ (here () .List.[]))
      ¬r◁Int ( _ , there _ _ (there _ _ ()))

  -- proof that Bool is derivable under the "Ambiguous" resolution rules
  ambiguous-can : Δ A.⊢ᵣ Bool
  ambiguous-can = r-ivar (there (here refl)) 

incomplete : ∃ λ ν → ∃₂ λ (Δ : ICtx ν) r → (Δ A.⊢ᵣ r) × (¬ Δ D.⊢ᵣ r)
incomplete = , (Δ , (Bool , (ambiguous-can , deterministic-cant)))
