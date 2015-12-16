open import Prelude

module Implicits.Semantics.Preservation
  (TC : Set)
  (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Syntax TC _tc≟_
open import Implicits.WellTyped TC _tc≟_
open import Implicits.Semantics.Type TC _tc≟_
open import Implicits.Semantics.Context TC _tc≟_
open import Implicits.Semantics.Lemmas TC _tc≟_
open import Implicits.Semantics.RewriteContext TC _tc≟_
open import Implicits.Semantics.Term TC _tc≟_
open import SystemF TC as F using ()

module Preservation
  (_⊢ᵣ_ : ∀ {ν} → ICtx ν → Type ν → Set)
  (⟦_,_⟧r : ∀ {ν n} {K : Ktx ν n} {a} → (proj₂ K) ⊢ᵣ a → K# K →
            ∃ λ t → ⟦ K ⟧ctx→ F.⊢ t ∈ ⟦ a ⟧tp→) where

  open TypingRules _⊢ᵣ_
  open TermSemantics _⊢ᵣ_ ⟦_,_⟧r

  -- interpretation of well-typed terms in System F preserves type
  ⟦⟧-preserves-tp : ∀ {ν n} {K : Ktx ν n} {t a} → (wt-t : K ⊢ t ∈ a) → (m : K# K) →
                    ⟦ K ⟧ctx→ F.⊢ ⟦ wt-t , m ⟧ ∈ ⟦ a ⟧tp→
  ⟦⟧-preserves-tp {K = K} (var x) m = subst-wt-var (sym $ lookup-⟦⟧ctx→ K x) (F.var x)
    where
      subst-wt-var = subst (λ a → ⟦ K ⟧ctx→ F.⊢ (F.var x) ∈ a)
  ⟦⟧-preserves-tp {K = K} {a = ∀' a} (Λ wt-e) m with ⟦⟧-preserves-tp wt-e (#tvar m)
  ... | ih = F.Λ (subst-wt-ctx (⟦weaken⟧ctx→ K) ih)
    where
      subst-wt-ctx = subst (λ c → c F.⊢ ⟦ wt-e , #tvar m ⟧ ∈ ⟦ a ⟧tp→)
  ⟦⟧-preserves-tp (λ' a wt-e) m with ⟦⟧-preserves-tp wt-e (#var a m)
  ⟦⟧-preserves-tp (λ' a wt-e) m | ih = F.λ' ⟦ a ⟧tp→ ih
  ⟦⟧-preserves-tp {K = K} (_[_] {a = a} wt-tc b) m with ⟦⟧-preserves-tp wt-tc m
  ... | ih = subst-tp (sym $ ⟦a/sub⟧tp→ a b) (ih F.[ ⟦ b ⟧tp→ ])
    where
      subst-tp = subst (λ c → ⟦ K ⟧ctx→ F.⊢ ⟦ wt-tc [ b ] , m ⟧ ∈ c) 
  ⟦⟧-preserves-tp (wt-f · wt-e) m with ⟦⟧-preserves-tp wt-f m | ⟦⟧-preserves-tp wt-e m
  ⟦⟧-preserves-tp (wt-f · wt-e) m | ih | y = ih F.· y
  ⟦⟧-preserves-tp (ρ a wt-e) m with ⟦⟧-preserves-tp wt-e (#ivar a m)
  ⟦⟧-preserves-tp (ρ a wt-e) m | ih = F.λ' ⟦ a ⟧tp→ ih
  ⟦⟧-preserves-tp (wt-r ⟨ e ⟩) m with ⟦⟧-preserves-tp wt-r m
  ⟦⟧-preserves-tp (wt-r ⟨ e ⟩) m | f-wt-r = f-wt-r F.· (proj₂ ⟦ e , m ⟧r)
  ⟦⟧-preserves-tp (wt-r with' wt-e ) m with ⟦⟧-preserves-tp wt-r m | ⟦⟧-preserves-tp wt-e m
  ⟦⟧-preserves-tp (wt-r with' wt-e ) m | f-wt-r | f-wt-e = f-wt-r F.· f-wt-e
  
