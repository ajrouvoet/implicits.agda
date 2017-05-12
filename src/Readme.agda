module Readme where

-- SystemF with small-step semantics
-- and normal forms
open import SystemF.Everything

-- SystemF extended with functions that take implicit parameters
-- including a reduction to SystemF
open import Implicits.Everything

-- Simply typed lambda calculus with references,
-- accompanied by a store-passing small-step semantics
open import STLCRef.Readme

-- First order dependently typed lambda calculus with references,
-- accompanied by a store-passing small-step semantics
-- and a proof that the small-step semantics is deterministic
open import LFRef.Readme
