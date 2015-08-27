open import Prelude hiding (Bool)

module Implicits.Oliveira.Improved.Deterministic (TC' : Set) (_tc≟'_ : (a b : TC') → Dec (a ≡ b)) where

{-
open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Improved.Resolution TC _tc≟_
open import Extensions.ListFirst
-}

-- This is more troublesome than I expected; the tricky thing is the rule r-simp.
-- r-simp requires an instance of first, which has 2 constructors:
--    (a) here: which relies on a proof that r can yield "a" (K ⊢ r ↓ a)
--    (b) there: which relies on a proof that r can NOT yield "a" (¬ K ⊢ r ↓ a)

-- Proving (b) deterministic is nonsensical. Check for example the example below:
-- (we give two ways to derive (b) for a single K, r and a)
-- Because (b) appears in _⊢ᵣ_, this makes _⊢ᵣ_ non-deterministic, which in turn makes
-- the r-iabs case of (a) non-deterministic.
-- The thing is that all non-determinism is situated in the "unhappy-path": (b).
-- Because the exact instance for (b) does not influence rule instantiation,
-- we should be able to give a weaker,
-- but still powerful enough, version of "equivalence" on derivations.

private

  data TC : Set where
    tc-int : TC
    tc-bool : TC

  _tc≟_ : (a b : TC) → Dec (a ≡ b)
  tc-int tc≟ tc-int = yes refl
  tc-int tc≟ tc-bool = no (λ ())
  tc-bool tc≟ tc-int = no (λ ())
  tc-bool tc≟ tc-bool = yes refl

  open import Data.Fin.Substitution
  open import Implicits.Oliveira.Types TC _tc≟_
  open import Implicits.Oliveira.Types.Unification TC _tc≟_
  open import Implicits.Oliveira.Terms TC _tc≟_
  open import Implicits.Oliveira.Contexts TC _tc≟_
  open import Implicits.Oliveira.Substitutions TC _tc≟_
  open import Implicits.Oliveira.Improved.Resolution TC _tc≟_
  open import Extensions.ListFirst

  Bool : Type 0
  Bool = simpl $ tc tc-bool

  Int : Type 0
  Int = simpl $ tc tc-int

  K : Ktx 0 1
  K = (Int ⇒ Bool) ∷K nil

  p₁ : ¬ (K ⊢ Int ⇒ Bool ↓ tc tc-int)
  p₁ (i-iabs (r-simp (here (i-iabs _ ()) .List.[])) _)
  p₁ (i-iabs (r-simp (there ._ _ ())) _)

  p₂ : ¬ (K ⊢ Int ⇒ Bool ↓ tc tc-int)
  p₂ (i-iabs x ())
