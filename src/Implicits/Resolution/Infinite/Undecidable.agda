module Implicits.Resolution.Infinite.Undecidable where

open import Prelude hiding (Bool; Dec)

open import Data.Fin.Substitution
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary.Decidable as DecM using ()
open import Relation.Nullary

open import Extensions.ListFirst
open import SystemF.Everything as F using ()

open import Implicits.Resolution.Ambiguous.Resolution as A
open import Implicits.Resolution.Deterministic.Resolution as D
open import Implicits.Resolution.Infinite.Resolution as I
open import Implicits.Syntax
open import Implicits.Substitutions
open import Implicits.Resolution.Ambiguous.Undecidable using () renaming (module Undecidable to AUndec)
open import Implicits.Resolution.Infinite.Expressiveness

private
  -- type of inhabitation problem decider
  ?:-dec : Set
  ?:-dec = ∀ {n ν} (Γ : F.Ctx ν n) (a : F.Type ν) → Dec (∃ λ t → Γ F.⊢ t ∈ a)

-- assuming that System F have an EBNF form
-- and assuming that System F type inhabitation is undecidable,
-- we prove that Infinite resolution is undecidable
module Undecidable
  (?:-undec : ¬ ?:-dec)
  (nf : ∀ {ν n} {Γ : F.Ctx ν n} {t a} → Γ F.⊢ t ∈ a → ∃ λ (t₂ : F.Term ν n) → Γ F.⊢ t₂ ⇑ a)
  where

  open Infinite⇔Ambiguous nf
  open AUndec ?:-undec using () renaming (undecidable to ⊢ᵣᵃ-undec; ⊢ᵣ-Dec to ⊢ᵣᵃ-Dec)

  -- type of decider for infinite resolution
  ⊢ᵣ-Dec : Set
  ⊢ᵣ-Dec = ∀ {ν} (Δ : ICtx ν) (a : Type ν) → Dec (Δ I.⊢ᵣ a)

  -- proof that such a decider would imply a decider for ambiguous resolution
  reduction : ⊢ᵣ-Dec → ⊢ᵣᵃ-Dec
  reduction f Δ x = DecM.map (equivalent Δ x) (f Δ x)

  -- completing the proof
  undecidable : ¬ ⊢ᵣ-Dec
  undecidable f =  ⊢ᵣᵃ-undec (reduction f)
