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

Bool : Type 0
Bool = simpl $ tc tc-bool

Int : Type 0
Int = simpl $ tc tc-int

-- We'll proof incompleteness with a simple example that we'll be able to resolve
-- using the ambigous resolution rules, but not with the deterministic rules.
-- This proofs that the ambiguous rules are stronger, such that together with Oliveira's
-- proof that determinstic resolution is sound w.r.t. ambiguous resolution, we have the
-- result that deterministic resolution is incomplete (or ambiguous resolution is strictly stronger)

module Example₁ where
  K : Ktx 0 2
  K = (Int ⇒ Bool) ∷K (Bool ∷K nil)

  module Deterministic where
    open import Implicits.Oliveira.Deterministic.Resolution TC _tc≟_
    open TypingRules _⊢ᵣ_
  
    -- proof that Bool is not derivable under the deterministic resolution rules
    p : ¬ (K ⊢ᵣ Bool)
    p (r-simp fst fst↓bool) with FirstLemmas.first-unique (l-head (m-iabs m-simp) (Bool List.∷ List.[])) fst
    p (r-simp fst (i-iabs (r-simp r _) b)) | refl = ¬r◁Int (, r)
      where
        ¬r◁Int : ¬ (∃ λ r → (proj₂ K) ⟨ tc tc-int ⟩= r)
        ¬r◁Int (._ , l-head (m-iabs ()) ._)
        ¬r◁Int (._ , l-tail _ (l-head () .List.[]))
        ¬r◁Int ( _ , l-tail _ (l-tail _ ()))
  
  module Ambiguous where
    open import Implicits.Oliveira.Ambiguous.Resolution TC _tc≟_
    open TypingRules _⊢ᵣ_
  
    -- proof that Bool is derivable under the "Ambiguous" resolution rules
    p : K ⊢ᵣ Bool
    p = r-ivar (there (here refl))
  
  -- just showing that the improved rules CAN derive Bool here
  module Improved where
    open import Implicits.Oliveira.Improved.Resolution TC _tc≟_
    open TypingRules _⊢ᵣ_
    open import Extensions.ListFirst
  
    ¬r₁ : ¬ K ⊢ (Int ⇒ Bool) ↓ tc tc-bool
    ¬r₁ (i-iabs (r-simp (here (i-iabs x ()) ._)) _)
    ¬r₁ (i-iabs (r-simp (there ._ _ (here () .List.[]))) _)
    ¬r₁ (i-iabs (r-simp (there ._ _ (there ._ _ ()))) _)
    
    p : K ⊢ᵣ Bool
    p = r-simp (there (Int ⇒ Bool) ¬r₁ (here (i-simp (tc tc-bool)) List.[]))