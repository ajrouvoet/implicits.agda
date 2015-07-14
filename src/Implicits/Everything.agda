module Implicits.Everything where

-- common agda stdlib imports
open import Prelude

-- examples of types and polymorphic type orderings
open import Examples.Types
-- examples of implicit derviations
open import Examples.Resolution

--
-- System F
--

-- the syntax
open import Implicits.SystemF.Types
open import Implicits.SystemF.Terms
open import Implicits.SystemF.Contexts

-- the well-typed relation
open import Implicits.SystemF.WellTyped

-- substitution stuff
open import Implicits.SystemF.Substitutions
open import Implicits.SystemF.Substitutions.Lemmas

-- the small step semantics + proof of soundness
open import Implicits.SystemF.SmallStep

--
-- The Calculus
--
open import Implicits.Calculus.Types
open import Implicits.Calculus.Terms
open import Implicits.Calculus.Contexts

-- subsitutions on types/terms/contexts
open import Implicits.Calculus.Substitutions
open import Implicits.Calculus.Substitutions.Lemmas

-- the well-typed relation
open import Implicits.Calculus.WellTyped

-- the denotational semantics
open import Implicits.Calculus.Denotational
