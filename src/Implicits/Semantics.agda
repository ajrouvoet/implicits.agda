open import Prelude

module Implicits.Semantics where

open import Implicits.Syntax
open import Implicits.WellTyped
open import Implicits.Semantics.Type public
open import Implicits.Semantics.Context public
open import Implicits.Semantics.RewriteContext public
open import Implicits.Semantics.Term public
open import Implicits.Semantics.Preservation public

open import SystemF.Everything as F using ()

module Semantics
  (_⊢ᵣ_ : ∀ {ν} → ICtx ν → Type ν → Set)
  (⟦_,_⟧r : ∀ {ν n} {K : Ktx ν n} {a} → (proj₂ K) ⊢ᵣ a → K# K →
            ∃ λ t → ⟦ proj₁ K ⟧ctx→ F.⊢ t ∈ ⟦ a ⟧tp→) where

  open TypingRules _⊢ᵣ_
  open TermSemantics _⊢ᵣ_ ⟦_,_⟧r public
  open Preservation _⊢ᵣ_ ⟦_,_⟧r public
