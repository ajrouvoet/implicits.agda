open import Prelude hiding (All; module All; _>>=_; ⊥)

module Implicits.Resolution.Infinite.Algorithm.Soundness where

open import Data.Bool
open import Data.Unit.Base
open import Coinduction
open import Data.Fin.Substitution
open import Data.List.Any
open import Implicits.Syntax
open import Implicits.Substitutions
open import Implicits.Substitutions.Lemmas
open import Implicits.Syntax.Type.Unification
open import Implicits.Resolution.Infinite.Resolution
open import Implicits.Resolution.Infinite.Algorithm
open Inductive

open import Category.Monad.Partiality as P
open import Category.Monad.Partiality.All using (All; module Alternative)
open Alternative renaming (sound to AllP-sound)

open import Extensions.Bool as Bl

resolve'-sound : ∀ {ν} (Δ : ICtx ν) r → AllP (AllTrue (Δ ⊢ᵣ r)) (resolve Δ r)
resolve'-sound Δ (simpl x) = {!!}
resolve'-sound Δ (a ⇒ b) = {!!}
resolve'-sound Δ (∀' r) = {!(resolve'-sound (ictx-weaken Δ) r) >>=-congP ?!}

-- Soundness means:
-- for all terminating runs of the algorithm we have a finite resolution proof.
-- We can make this formal using the *inductive* resolution rules
sound : ∀ {ν} (Δ : ICtx ν) r → All (AllTrue (Δ ⊢ᵣ r)) (resolve Δ r)
sound Δ r = AllP-sound (resolve'-sound Δ r)
