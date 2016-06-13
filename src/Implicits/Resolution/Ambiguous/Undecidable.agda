module Implicits.Resolution.Ambiguous.Undecidable where

open import Prelude

open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary.Decidable as Dec using ()
open import Relation.Binary.HeterogeneousEquality as H using ()

open import Implicits.Syntax
open import Implicits.Resolution.Ambiguous.Resolution
open import Implicits.Resolution.Ambiguous.Semantics
open import Implicits.Resolution.Ambiguous.SystemFEquiv
open import Implicits.Resolution.Embedding
open import Implicits.Resolution.Embedding.Lemmas

open import SystemF as F using ()
  
{-
  Assuming undecidability of the type inhabitation problem for System F
  (as proven by e.g. Barendregt) we can prove the undecidability of Ambiguous resolution
-}

private
  -- type of inhabitation problem decider
  ?:-Dec : Set
  ?:-Dec = ∀ {n ν} (Γ : F.Ctx ν n) (a : F.Type ν) → Dec (∃ λ t → Γ F.⊢ t ∈ a)

module Undecidable (?:-undec : ¬ ?:-Dec) where

  -- type of decider for ambiguous resolution
  ⊢ᵣ-Dec : Set
  ⊢ᵣ-Dec = ∀ {ν} (Δ : ICtx ν) (a : Type ν) → Dec (Δ ⊢ᵣ a)

  -- proof that such a decider would imply a decider for type inhabitation problem
  reduction : ⊢ᵣ-Dec → ?:-Dec
  reduction f Γ x = Dec.map (equivalent' Γ x) (f ⟦ Γ ⟧ctx← ⟦ x ⟧tp←)

  -- completing the proof
  undecidable : ¬ ⊢ᵣ-Dec
  undecidable f = ?:-undec (reduction f) 
