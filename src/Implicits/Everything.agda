module Implicits.Everything where

-- common agda stdlib imports
open import Prelude

-- We give a well-scoped version of Oliveira's ambiguous and deterministic
-- resolution rules
open import Implicits.Oliveira.Ambiguous.Resolution
open import Implicits.Oliveira.Deterministic.Resolution

-- we show that Oliveira's deterministic rules are incomplete w.r.t.
-- the ambiguous resolution
open import Implicits.Oliveira.Deterministic.Incomplete

-- We then present a coinductive set of resolution rules, modeled
-- after Oliveira's deterministic rules.
-- We maintain the syntax-directedness of the rules and strenghten the hypothesis of r-simp
-- to circumvent the weakness of Oliveira's deterministic rules.
-- In order to maintain strict-positiveness of the rules, we drop determinacy.
-- We will regain determinacy in the algorithmic description of resolution.
open import Implicits.Improved.Ambiguous.Resolution
open SyntaxDirected

-- By strengthening r-simp's hypothesis, we make the rules more powerful (but resolution
-- is more difficult).
-- We observe that we have an opportunity to make resolution even more powerful by removing
-- the termination constraint from the environment and enforcing it on resolution 'stacks'.
-- The latter constraint is less restrictive because it works on instantiated rules:
-- i.e. there is no need for a rule to be terminating for *all* possible instantiations, as long
-- as it terminates for the current instantiation.

-- We show that the coinductive rules are complete w.r.t. the deterministic rules
open import Implicits.Improved.Ambiguous.Expressiveness
-- An open question is whether the coinductive rules are complete w.r.t. the ambiguous rules,
-- in the sense: Δ Ambiguous.⊢ᵣ r → Δ Coinductive.⊢ᵣ r

-- Furthermore we give a partial algorithm A₁ for Δ Coinductive.⊢ᵣ r
-- The type guarantees soundness, but the algorithm may never terminate
-- even for finite resolutions
open import Implicits.Improved.Ambiguous.PartialResolution
-- We'd love to show that the existence of a finite resolution Δ ⊢ᵣ r guarantees
-- termination of the partial resolution algorithm on input r;
-- but this clearly isn't a theorem: it's easy to imagine an implicit context that both has
-- a diverging 'trap' for the deterministic algorithm but also allows a finite 'shortcut'
-- derivation (hiding behind the trap).

-- Instead we define a decidable predicate F (for finite) on coinductive resolutions that guarantees
-- that it's finite.
-- No decidable predicate can select exactly the finite subset of the coinductive resolutions.
-- So F will be a sufficient, but not a necessary condition for finiteness.
-- We are confident that the set of decidably finite resolutions (DFR) is bigger than the set of
-- deterministic resolutions (under the environmental termination constraint) as proposed by
-- Oliveira et al.
-- We aim to give a partial resolution algorithm A₂ that is sound & complete w.r.t. de set DFR.

-- examples of types and polymorphic type orderings
open import Examples.Types
open import Examples.PartialResolution
