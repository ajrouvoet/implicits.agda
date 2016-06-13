open import Prelude 

module Implicits.Resolution.Scala.Terminates where

open import Implicits.Syntax
open import Implicits.Substitutions
open import Implicits.Resolution.Infinite.Algorithm
open import Implicits.Resolution.Scala.Type
open import Category.Monad.Partiality

open import Category.Monad.Partiality as P
open Workaround
open import Category.Monad.Partiality.All using (All; module Alternative)
open Alternative renaming (sound to AllP-sound) hiding (complete)

private
  open import Relation.Binary.PropositionalEquality as PEq using (_≡_)
  open module PartialEq = P.Equality  {A = Bool} _≡_
  open module PartialReasoning  = P.Reasoning (PEq.isEquivalence {A = Bool})

match-terminates : ∀ {ν} (Δ : ICtx ν) → (τ : SimpleType ν) → (r : Type ν) → (match Δ τ r) ⇓
match-terminates Δ τ r = ?

match1st-terminates : ∀ {ν} (Δ : ICtx ν) → (ρs : ICtx ν) → (τ : SimpleType ν) → (match1st Δ ρs τ) ⇓
match1st-terminates Δ List.[] τ = false , (now refl)
match1st-terminates Δ (x List.∷ ρs) τ = {!!}

terminates : ∀ {ν} (Δ : ICtx ν) (a : Type ν) → ScalaICtx Δ → ScalaType a → (resolve Δ a) ⇓
terminates Δ (simpl x) p q = match1st-terminates Δ Δ x
terminates Δ (∀' a) p (∀' q) = terminates (ictx-weaken Δ) a (weaken-scalaictx p) q
terminates Δ (a ⇒ b) p ()
