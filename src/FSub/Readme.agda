module FSub.Readme where

-- We extend the SystemF types with Top and Bot and
-- add an upperbound to type-abstraction
open import FSub.Types

-- Then we define semantics for 3 flavors of FSub, each flavor
-- taken to be one from the crossproduct
-- {intrinsic, extrinsic} × {algorithmic, declarative}
-- We only consider *kernel F<:*, where subtyping for type-abstraction
-- is only defined for constant upperbounds:
--
--          Γ , α <: u ⊢ a <: a'
-- ---------------------------------------
--  Γ ⊢ ∀ (α <: u) . a <: ∀ (α <: u) . a'

open import FSub.Types.Subtyping
open Declarative
open Algorithmic

--open import FSub.Extrinsic.Declarative.Properties.Sound
--open import FSub.Intrinsic.Declarative.Semantics
--open import FSub.Intrinsic.Algorithmic.Semantics
