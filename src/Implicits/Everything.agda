module Implicits.Everything where

-- common agda stdlib imports
open import Prelude

--
-- Oliveira's calculi in Agda
--

-- We give a well-scoped version of Oliveira's ambiguous and deterministic
-- resolution rules
open import Implicits.Resolution.Ambiguous.Resolution
open import Implicits.Resolution.Deterministic.Resolution

-- and prove soundness of det. resolution w.r.t the ambiguous one
open import Implicits.Resolution.Deterministic.Expressiveness

-- we show that Oliveira's deterministic rules are incomplete w.r.t.
-- the ambiguous resolution
open import Implicits.Resolution.Deterministic.Incomplete

--
-- Partial resolution
--

-- We maintain the syntax-directedness of the rules and strenghten the hypothesis of r-simp
-- to circumvent the weakness of Oliveira's deterministic rules.
-- In order to maintain strict-positiveness of the rules, we drop determinacy.
-- We will regain determinacy in the algorithmic description of resolution.
open import Implicits.Resolution.Infinite.Resolution

-- We first show that the rules are isomorphic to EBNF System F expressions
-- and use it to prove that infinite resolution is complete w.r.t. ambiguous resolution.
open import Implicits.Resolution.Infinite.NormalFormIso
open import Implicits.Resolution.Infinite.Expressiveness

-- Furthermore we give a partial algorithm for infinite resolution.
-- We have soundness and partial completeness for this algorithm.
open import Implicits.Resolution.Infinite.Algorithm
open import Implicits.Resolution.Infinite.Algorithm.Soundness
-- open import Implicits.Resolution.Infinite.Algorithm.Completeness

-- We'd love to show that the existence of a finite resolution Δ ⊢ᵣ r guarantees
-- termination of the partial resolution algorithm on input r;
-- but this clearly isn't a theorem: it's easy to imagine an implicit context that both has
-- a diverging 'trap' for the deterministic algorithm but also allows a finite 'shortcut'
-- derivation (hiding behind the trap).
-- In fact, the fact that infinite resolution is complete w.r.t. Ambiguous resolution, indirectly proves-- that it's undecidable.

-- open import Examples.PartialResolution
-- open import Examples.CompleteResolution
