open import Prelude hiding (id; Bool)

module Implicits.Oliveira.Deterministic.Incomplete where

data TC : Set where
  tc-int : TC
  tc-bool : TC

_tc≟_ : (a b : TC) → Dec (a ≡ b)
tc-int tc≟ tc-int = yes refl
tc-int tc≟ tc-bool = no (λ ())
tc-bool tc≟ tc-int = no (λ ())
tc-bool tc≟ tc-bool = yes refl

open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.WellTyped TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
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

K : Ktx 0 2
K = (Int ⇒ Bool) ∷K (Bool ∷K nil)

module Deterministic where
  open import Implicits.Oliveira.Deterministic.Resolution TC _tc≟_
  open TypingRules _⊢ᵣ_

  p : ¬ (K ⊢ᵣ Bool)
  p (r-simp fst fst↓bool) with FirstLemmas.first-unique (here (m-iabs m-simp) List.[ Bool ]) fst
  p (r-simp fst (i-iabs (r-simp r _) b)) | refl = ¬r◁Int (, r)
    where
      ¬r◁Int : ¬ (∃ λ r → K ⟨ tc tc-int ⟩= r)
      ¬r◁Int (._ , here (m-iabs ()) ._)
      ¬r◁Int (._ , there ._ _ (here () .List.[]))
      ¬r◁Int ( _ , there ._ _ (there .(simpl (tc tc-bool)) _ ()))

module Ambiguous where
  open import Implicits.Oliveira.Ambiguous.Resolution TC _tc≟_
  open TypingRules _⊢ᵣ_

  p : K ⊢ᵣ Bool
  p = r-ivar (there (here refl))



