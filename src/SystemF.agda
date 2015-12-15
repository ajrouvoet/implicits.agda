module SystemF (TC : Set) where

open import SystemF.Syntax.Type.Constructors TC public
open import SystemF.Syntax.Term.Constructors TC public
open import SystemF.WellTyped TC public
open import SystemF.Substitutions.Lemmas TC public
open import SystemF.Substitutions TC public
open TypeLemmas public hiding (var)
