module Implicits.Everything where

-- common agda stdlib imports
open import Prelude

--
-- Oliveira's work in Agda
--

-- We give a well-scoped version of Oliveira's ambiguous and deterministic
-- resolution rules
open import Implicits.Oliveira.Ambiguous.Resolution
open import Implicits.Oliveira.Deterministic.Resolution

-- and prove soundness of det. resolution w.r.t the ambiguous one
open import Implicits.Oliveira.Deterministic.Expressiveness

-- we show that Oliveira's deterministic rules are incomplete w.r.t.
-- the ambiguous resolution
open import Implicits.Oliveira.Deterministic.Incomplete

--
-- Coinductive (partial) resolution
--

-- We then present a coinductive set of resolution rules, modeled
-- after Oliveira's deterministic rules.
-- We maintain the syntax-directedness of the rules and strenghten the hypothesis of r-simp
-- to circumvent the weakness of Oliveira's deterministic rules.
-- In order to maintain strict-positiveness of the rules, we drop determinacy.
-- We will regain determinacy in the algorithmic description of resolution.
open import Implicits.Improved.Infinite.Resolution

-- By strengthening r-simp's hypothesis, we make the rules more powerful (but resolution
-- is more difficult).
-- We observe that we have an opportunity to make resolution even more powerful by removing
-- the termination constraint from the environment and enforcing it on resolution 'stacks'.
-- The latter constraint is less restrictive because it works on instantiated rules:
-- i.e. there is no need for a rule to be terminating for *all* possible instantiations, as long
-- as it terminates for the current instantiation.

-- We show that the coinductive rules are complete w.r.t. the deterministic rules
open import Implicits.Improved.Infinite.Expressiveness
-- An open question is whether the coinductive rules are complete w.r.t. the ambiguous rules,
-- in the sense: Δ Ambiguous.⊢ᵣ r → Δ Coinductive.⊢ᵣ r

-- Furthermore we give a partial algorithm A₁ for Δ Coinductive.⊢ᵣ r
-- The type guarantees soundness, but the algorithm may never terminate
-- even for finite resolutions
open import Implicits.Improved.Infinite.Algorithm
-- We'd love to show that the existence of a finite resolution Δ ⊢ᵣ r guarantees
-- termination of the partial resolution algorithm on input r;
-- but this clearly isn't a theorem: it's easy to imagine an implicit context that both has
-- a diverging 'trap' for the deterministic algorithm but also allows a finite 'shortcut'
-- derivation (hiding behind the trap).

--
-- Inductive (decidable) resolution
--

-- We then present an ambiguous, syntax-directed and inductive version of resolution.
-- Very similar to the coinductive rules, but with an added hypothesis for using rules,
-- ensuring that recursive use of rules is only allowed if the goal is shrinking
open import Implicits.Improved.Finite.Resolution

-- We give an algorithm for it
open import Implicits.Improved.Finite.Algorithm

-- examples of types and polymorphic type orderings
open import Examples.Types
open import Examples.PartialResolution
open import Examples.CompleteResolution
