open import Prelude
open import Data.List.Properties
open import Data.List.Any hiding (map)

module Implicits.Resolution.Ambiguous.Semantics TC _tc≟_ where

open import Implicits.Syntax TC _tc≟_
open import Implicits.Resolution.Ambiguous.Resolution TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open import Implicits.Substitutions.Lemmas TC _tc≟_
open import Implicits.Semantics TC _tc≟_
open import Implicits.Semantics.Lemmas TC _tc≟_

open import SystemF TC as F using ()

module DerivationSemantics where

  ⟦_,_⟧r : ∀ {ν n} {K : Ktx ν n} {a} → (proj₂ K) ⊢ᵣ a → K# K →
           ∃ λ t → ⟦ K ⟧ctx→ F.⊢ t ∈ ⟦ a ⟧tp→
  ⟦_,_⟧r {K = K} (r-tabs {r = r} p) m with ⟦ p , #tvar m ⟧r
  ⟦_,_⟧r {K = K} (r-tabs {r = r} p) m | _ , x =
    , F.Λ (subst (λ u → u F.⊢ _ ∈ ⟦ r ⟧tp→) (⟦weaken⟧ctx→ K) x) 
  ⟦_,_⟧r {K = K} (r-tapp a p) m with ⟦ p , m ⟧r
  ⟦_,_⟧r {K = K} (r-tapp {r = a} b p) m | _ , x = 
    , subst
      (λ u → ⟦ K ⟧ctx→ F.⊢ _ ∈ u)
      (sym $ ⟦a/sub⟧tp→ a b)
      (x F.[ ⟦ b ⟧tp→ ])
  ⟦_,_⟧r {K = K} {a = a} (r-ivar x) m with ∈⟶index (All.lookup m x)
  ⟦_,_⟧r {K = K} {a = a} (r-ivar x) m | i , lookup-i≡r =
    , subst (λ u → _ F.⊢ F.var i ∈ u) eq (F.var i)
    where
      eq = begin 
        lookup i ⟦ K ⟧ctx→
          ≡⟨ sym $ lookup-⟦⟧ctx→ K i ⟩
        ⟦ lookup i (proj₁ K) ⟧tp→
            ≡⟨ cong ⟦_⟧tp→ lookup-i≡r ⟩
        ⟦ a ⟧tp→ ∎ 
  ⟦_,_⟧r (r-iabs {a = a} p) m = , F.λ' ⟦ a ⟧tp→ (proj₂ ⟦ p , #ivar a m ⟧r)
  ⟦_,_⟧r (r-iapp p p₁) m = , (proj₂ ⟦ p , m ⟧r) F.· (proj₂ ⟦ p₁ , m ⟧r)

open Semantics _⊢ᵣ_ DerivationSemantics.⟦_,_⟧r public
