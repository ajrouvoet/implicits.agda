open import Prelude

module Implicits.Semantics.Denotational
  (TC : Set)
  (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Syntax TC _tc≟_
open import Implicits.WellTyped TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open import Implicits.Substitutions.Lemmas TC _tc≟_
open import Implicits.Semantics.Type TC _tc≟_
open import Implicits.Semantics.Context TC _tc≟_
open import Implicits.Semantics.Lemmas TC _tc≟_
open import Implicits.Semantics.RewriteContext TC _tc≟_
open import SystemF TC as F using ()
open import Extensions.ListFirst
open import Data.Fin.Substitution
open import Data.Vec.Properties

module TSS = Simple TS.simple
module FTSS = Simple F.simple

module Semantics
  (_⊢ᵣ_ : ∀ {ν} → ICtx ν → Type ν → Set)
  (⟦_,_⟧r : ∀ {ν n} {K : Ktx ν n} {a} → (proj₂ K) ⊢ᵣ a → K# K → ∃ λ t → ⟦ K ⟧ctx F.⊢ t ∈ ⟦ a ⟧tp→) where

  open TypingRules _⊢ᵣ_

  -- denotational semantics of well-typed terms
  ⟦_,_⟧ : ∀ {ν n} {K : Ktx ν n} {t} {a : Type ν} → K ⊢ t ∈ a → K# K → F.Term ν n
  ⟦_,_⟧ (var x) m = F.var x
  ⟦_,_⟧ (Λ t) m = F.Λ ⟦ t , #tvar m ⟧
  ⟦_,_⟧ (λ' a x) m = F.λ' ⟦ a ⟧tp→ ⟦ x , #var a m ⟧
  ⟦_,_⟧ (f [ b ]) m = F._[_] ⟦ f , m ⟧ ⟦ b ⟧tp→
  ⟦_,_⟧ (f · e) m = ⟦ f , m ⟧ F.· ⟦ e , m ⟧
  ⟦_,_⟧ (ρ a x) m = F.λ' ⟦ a ⟧tp→ ⟦ x , #ivar a m ⟧
  ⟦_,_⟧ (f ⟨ e∈Δ ⟩) m = ⟦ f , m ⟧ F.· (proj₁ ⟦ e∈Δ , m ⟧r)
  ⟦_,_⟧ (_with'_ r e) m = ⟦ r , m ⟧ F.· ⟦ e , m ⟧
  
  -- interpretation of well-typed terms in System F preserves type
  ⟦⟧-preserves-tp : ∀ {ν n} {K : Ktx ν n} {t a} → (wt-t : K ⊢ t ∈ a) → (m : K# K) →
                    ⟦ K ⟧ctx F.⊢ ⟦ wt-t , m ⟧ ∈ ⟦ a ⟧tp→
  ⟦⟧-preserves-tp {K = K} (var x) m = subst-wt-var (lookup⋆⟦⟧ctx K x) (F.var x)
    where
      subst-wt-var = subst (λ a → ⟦ K ⟧ctx F.⊢ (F.var x) ∈ a)
  ⟦⟧-preserves-tp {K = K} {a = ∀' a} (Λ wt-e) m with ⟦⟧-preserves-tp wt-e (#tvar m)
  ... | ih = F.Λ (subst-wt-ctx (ctx-weaken⋆⟦⟧ctx K) ih)
    where
      subst-wt-ctx = subst (λ c → c F.⊢ ⟦ wt-e , #tvar m ⟧ ∈ ⟦ a ⟧tp→)
  ⟦⟧-preserves-tp (λ' a wt-e) m with ⟦⟧-preserves-tp wt-e (#var a m)
  ⟦⟧-preserves-tp (λ' a wt-e) m | ih = F.λ' ⟦ a ⟧tp→ ih
  ⟦⟧-preserves-tp {K = K} (_[_] {a = a} wt-tc b) m with ⟦⟧-preserves-tp wt-tc m
  ... | ih = subst-tp (sym $ ⟦sub⟧≡sub⟦⟧ a b) (ih F.[ ⟦ b ⟧tp→ ])
    where
      subst-tp = subst (λ c → ⟦ K ⟧ctx F.⊢ ⟦ wt-tc [ b ] , m ⟧ ∈ c) 
  ⟦⟧-preserves-tp (wt-f · wt-e) m with ⟦⟧-preserves-tp wt-f m | ⟦⟧-preserves-tp wt-e m
  ⟦⟧-preserves-tp (wt-f · wt-e) m | ih | y = ih F.· y
  ⟦⟧-preserves-tp (ρ a wt-e) m with ⟦⟧-preserves-tp wt-e (#ivar a m)
  ⟦⟧-preserves-tp (ρ a wt-e) m | ih = F.λ' ⟦ a ⟧tp→ ih
  ⟦⟧-preserves-tp (wt-r ⟨ e ⟩) m with ⟦⟧-preserves-tp wt-r m
  ⟦⟧-preserves-tp (wt-r ⟨ e ⟩) m | f-wt-r = f-wt-r F.· (proj₂ ⟦ e , m ⟧r)
  ⟦⟧-preserves-tp (wt-r with' wt-e ) m with ⟦⟧-preserves-tp wt-r m | ⟦⟧-preserves-tp wt-e m
  ⟦⟧-preserves-tp (wt-r with' wt-e ) m | f-wt-r | f-wt-e = f-wt-r F.· f-wt-e
  
