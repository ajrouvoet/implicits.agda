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

-- and prove ambiguous resolution undecidable
open import Implicits.Resolution.Ambiguous.SystemFEquiv
open import Implicits.Resolution.Ambiguous.Undecidable

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
open import Implicits.Resolution.Infinite.NormalFormEquiv
open import Implicits.Resolution.Infinite.Expressiveness

-- Furthermore we give a partial algorithm for infinite resolution.
-- We have soundness and develop partial completeness for this algorithm.
open import Implicits.Resolution.Infinite.Algorithm
open import Implicits.Resolution.Infinite.Algorithm.Soundness
-- open import Implicits.Resolution.Infinite.Algorithm.Completeness

-- We'd love to show that the existence of a finite resolution Δ ⊢ᵣ r guarantees
-- termination of the partial resolution algorithm on input r;
-- but this clearly isn't a theorem: it's easy to imagine an implicit context that both has
-- a diverging 'trap' for the deterministic algorithm but also allows a finite 'shortcut'
-- derivation (hiding behind the trap).
-- In fact, the fact that infinite resolution is complete w.r.t. Ambiguous resolution,
-- indirectly proves that it's undecidable.

-- Instead we define a version of infinite resolution with a generic termination condition
open import Implicits.Resolution.GenericFinite.TerminationCondition
open import Implicits.Resolution.GenericFinite.Resolution
open import Implicits.Resolution.GenericFinite.Expressiveness

-- We give a total algorithm and prove it sound
open import Implicits.Resolution.GenericFinite.Algorithm
open import Implicits.Resolution.GenericFinite.Algorithm.Soundness
-- and develop completeness; finished modulo 2 lemmas
-- open import Implicits.Resolution.GenericFinite.Algorithm.Completeness

-- We provide two examples of termination conditions
-- A simple "maximum depth" condition like Coq's auto tactic has:
open import Implicits.Resolution.GenericFinite.Examples.MaximumDepth
-- And basically a termination condition inspired by Haskell's conditions on
-- typeclasses, developed by Oliveira et al.
-- Importantly we prove that the resulting calculus is more expressive than
-- Oliveira's deterministic resolution
open import Implicits.Resolution.GenericFinite.Examples.Haskell

-- We define a denotation semantics for the entire calculus -- into System F.
-- To this end we develop System F:
open import SystemF.Syntax
open import SystemF.WellTyped
open import SystemF.SmallStep
open import SystemF.NormalForm

-- The actual semantics is implemented aa module that depends on
-- the semantics for your favorite flavor of resolution.
-- It includes a proof that the translation preserves the typing relation.
open import Implicits.Semantics.Preservation
open import Implicits.Semantics
