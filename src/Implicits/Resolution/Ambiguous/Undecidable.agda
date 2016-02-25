module Implicits.Resolution.Ambiguous.Undecidable where

open import Prelude

open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary.Decidable as Dec using ()

open import Implicits.Syntax
open import Implicits.Resolution.Ambiguous.Resolution
open import Implicits.Resolution.Ambiguous.Semantics
open import Implicits.Resolution.Ambiguous.SystemFIso
open import Implicits.Resolution.Embedding
open import Implicits.Resolution.Embedding.Lemmas

open import SystemF as F using ()
  
{-
  Assuming undecidability of the type inhabitation problem for System F
  (as proven by e.g. Barendregt) we can prove the undecidability of Ambiguous resolution
-}

private
  -- type of inhabitation problem decider
  ?:-dec : Set
  ?:-dec = ∀ {ν} → (a : F.Type ν) → Dec (∃ λ t → [] F.⊢ t ∈ a)

module Undecidable (?:-undec : ¬ ?:-dec) where

  -- type of decider for ambiguous resolution
  ⊢ᵣ-dec : Set
  ⊢ᵣ-dec = ∀ {ν} (Δ : ICtx ν) → (a : Type ν) → Dec (Δ ⊢ᵣ a)

  -- proof that such a decider would imply a decider for type inhabitation problem
  reduction : ⊢ᵣ-dec → ?:-dec
  reduction f x = Dec.map (
    subst
      (λ u → List.[] ⊢ᵣ ⟦ x ⟧tp← ⇔ ∃ (λ t → [] F.⊢ t ∈ u))
      (tp←→ x)
      (iso List.[] ⟦ x ⟧tp←)) (f List.[] ⟦ x ⟧tp←)

  -- completing the proof
  undecidable : ¬ ⊢ᵣ-dec
  undecidable f = ?:-undec (reduction f) 
