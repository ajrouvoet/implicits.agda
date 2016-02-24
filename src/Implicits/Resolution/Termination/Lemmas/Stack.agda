open import Prelude

module Implicits.Resolution.Termination.Lemmas.Stack
  where

open import Induction.WellFounded
open import Induction.Nat
open import Data.Fin.Substitution
open import Implicits.Syntax
open import Implicits.Substitutions
open import Implicits.Substitutions.Lemmas
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties

open import Implicits.Resolution.Termination.SizeMeasures
open import Implicits.Resolution.Termination.Stack


open import Data.Nat.Base
+k<+k : ∀ {n m} k → n N< m → k N+ n N< k N+ m
+k<+k zero p = p
+k<+k (suc k) p = s≤s (+k<+k k p)

+k<+k' : ∀ {n m} k → n N< m → n N+ k N< m N+ k
+k<+k' {n} {m} k p = subst₂ (λ u v → u N< v) (+-comm k n) (+-comm k m) (+k<+k k p)
  where open import Data.Nat.Properties.Simple

-k<-k : ∀ {n m} k → k N+ n N< k N+ m → n < m
-k<-k zero x = x
-k<-k (suc k) (s≤s x) = -k<-k k x

-k<-k' : ∀ {n m} k → n N+ k N< m N+ k → n < m
-k<-k' {n} {m} k p = -k<-k k (subst₂ _N<_ (+-comm n k) (+-comm m k) p) 
  where open import Data.Nat.Properties.Simple

----------------------------------------------------------------
-- stack properties

push< : ∀ {ν r a} {Δ : ICtx ν} (s : Stack Δ) (r∈Δ : r List.∈ Δ) →
        (, a) ρ< (, s get r∈Δ) → (s push a for r∈Δ) s< s
push< (b All.∷ s) (here _) a<b = +k<+k' (ssum s) a<b
push< (b All.∷ s) (there r∈Δ) p = +k<+k h|| b || (push< s r∈Δ p)

push≮ : ∀ {ν r a} {Δ : ICtx ν} (s : Stack Δ) (r∈Δ : r List.∈ Δ) →
        ¬ ((, a) ρ< (, s get r∈Δ)) → ¬ (s push a for r∈Δ) s< s
push≮ (b All.∷ s) (here _) ¬a<b = λ x → ¬a<b (-k<-k' (ssum s) x)
push≮ (b All.∷ s) (there r∈Δ) ¬a<b = λ x → push≮ s r∈Δ ¬a<b (-k<-k h|| b || x)

----------------------------------------------------------------
-- a type dominates a stack if pushing it to the stack makes the stack bigger

_for_?⊬dom_ : ∀ {ν r} {Δ : ICtx ν} → (a : Type ν) → (r∈Δ : r List.∈ Δ) → (s : Stack Δ) →
               Dec (a for r∈Δ ⊬dom s)
a for r∈Δ ?⊬dom s with (, a) ρ<? (, s get r∈Δ)
a for r∈Δ ?⊬dom s | yes p = yes (push< s r∈Δ p)
a for r∈Δ ?⊬dom s | no ¬p = no (push≮ s r∈Δ ¬p)


-- we also show that the ordering on stacks is well founded
s<-well-founded : ∀ {ν} {Δ : ICtx ν} → Well-founded (_s<_ {ν} {Δ})
s<-well-founded = sub.well-founded (image.well-founded <-well-founded)
  where
    open import Data.Nat.Base
    open import Data.Nat.Properties
    module sub = Inverse-image (λ{ s → ssum s})
    module image = Subrelation {A = ℕ} {_N<_} {_<′_} ≤⇒≤′

{-}
-- we can show that our strict size measure a ρ< b is well founded
-- by relating it to the well-foundedness proof of _<'_
sρ<-well-founded : Well-founded _sρ<_
sρ<-well-founded = sub.well-founded (image.well-founded <-well-founded)
  where
    module sub = Inverse-image (λ{ (_ , a) → || a ||})
    module image = Subrelation {A = ℕ} {_N<_} {_<′_} ≤⇒≤′
-}
