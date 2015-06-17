module Implicits.Everything where

-- common agda stdlib imports
open import Prelude

--
-- System F
--

-- the syntax
open import Implicits.SystemF.Types
open import Implicits.SystemF.Terms
open import Implicits.SystemF.Contexts

-- the well-typed relation
open import Implicits.SystemF.WellTyped

-- the small step semantics + proof of soundness
open import Implicits.SystemF.SmallStep

--
-- The Calculus
--
open import Implicits.Calculus.Types
open import Implicits.Calculus.Terms
open import Implicits.Calculus.Contexts

-- the well-typed relation
open import Implicits.Calculus.WellTyped

-- the denotational semantics
open import Implicits.Calculus.Denotational
