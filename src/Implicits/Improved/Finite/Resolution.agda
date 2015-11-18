open import Prelude

module Implicits.Improved.Finite.Resolution (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Coinduction
open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Induction
open import Induction.Nat
open import Relation.Binary using (Rel)

Stack' : ∀ {ν} → ICtx ν → Set
Stack' {ν} Δ = All (const $ Type ν) Δ

----------------------------------------------------------------
-- basic stack operations

_push_for_ : ∀ {ν r} {Δ : ICtx ν} → Stack' Δ → Type ν → r List.∈ Δ → Stack' Δ
(a All.∷ s) push a' for here _ = a' All.∷ s
(b All.∷ s) push a for there r∈Δ = b All.∷ s push a for r∈Δ

_prepend_ : ∀ {ν r} {Δ : ICtx ν} → Stack' Δ → Type ν → Stack' (r List.∷ Δ)
s prepend a = a All.∷ s

_get_ : ∀ {ν r} {Δ : ICtx ν} → Stack' Δ → r List.∈ Δ → Type ν
(a All.∷ s) get here _ = a 
(a All.∷ s) get there r∈Δ = s get r∈Δ

ssum : ∀ {ν} {Δ : ICtx ν} → Stack' Δ → ℕ
ssum All.[] = 0
ssum (a All.∷ s) = h|| a || N+ ssum s

stack-weaken : ∀ {ν} {Δ : ICtx ν} → Stack' Δ → Stack' (ictx-weaken Δ)
stack-weaken All.[] = All.[]
stack-weaken (px All.∷ s) = (tp-weaken px) All.∷ (stack-weaken s)

----------------------------------------------------------------
-- stack ordering

_s<_ : ∀ {ν} {Δ : ICtx ν} → (s s' : Stack' Δ) → Set
s s< s' = ssum s N< ssum s'

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

push< : ∀ {ν r a} {Δ : ICtx ν} (s : Stack' Δ) (r∈Δ : r List.∈ Δ) →
        a ρ< (s get r∈Δ) → (s push a for r∈Δ) s< s
push< (b All.∷ s) (here _) a<b = +k<+k' (ssum s) a<b
push< (b All.∷ s) (there r∈Δ) p = +k<+k h|| b || (push< s r∈Δ p)

push≮ : ∀ {ν r a} {Δ : ICtx ν} (s : Stack' Δ) (r∈Δ : r List.∈ Δ) →
        ¬ (a ρ< (s get r∈Δ)) → ¬ (s push a for r∈Δ) s< s
push≮ (b All.∷ s) (here _) ¬a<b = λ x → ¬a<b (-k<-k' (ssum s) x)
push≮ (b All.∷ s) (there r∈Δ) ¬a<b = λ x → push≮ s r∈Δ ¬a<b (-k<-k h|| b || x)

----------------------------------------------------------------
-- a type dominates a stack if pushing it to the stack makes the stack bigger

_for_⊬dom_ : ∀ {ν r} {Δ : ICtx ν} → Type ν → r List.∈ Δ → Stack' Δ → Set
a for r∈Δ ⊬dom s = (s push a for r∈Δ) s< s

_for_?⊬dom'_ : ∀ {ν r} {Δ : ICtx ν} → (a : Type ν) → (r∈Δ : r List.∈ Δ) → (s : Stack' Δ) →
               Dec (a for r∈Δ ⊬dom s)
a for r∈Δ ?⊬dom' s with a ρ<? (s get r∈Δ)
a for r∈Δ ?⊬dom' s | yes p = yes (push< s r∈Δ p)
a for r∈Δ ?⊬dom' s | no ¬p = no (push≮ s r∈Δ ¬p)

infixl 5 _⊢ᵣ_
infixl 5 _&_⊢ᵣ_ _&_,_⊢_↓_
mutual

  -- Δ & s , r ⊢ a ↓ τ denotes:
  -- Under the context Δ, with stack of resolution goals s, the type a yields simple type τ.
  -- 'r' is used to keep track of the rule from the context that yielded 'a'
  -- ('a' is getting recursively refined)
  data _&_,_⊢_↓_ {ν} (Δ : ICtx ν) :
    ∀ {r} → Stack' Δ → r List.∈ Δ → Type ν → SimpleType ν → Set where

    i-simp : ∀ {r s} {r∈Δ : r List.∈ Δ} a → Δ & s , r∈Δ ⊢ simpl a ↓ a
    i-iabs : ∀ {ρ₁ ρ₂ a r s} {r∈Δ : r List.∈ Δ} →
             ρ₁ for r∈Δ ⊬dom s → -- subproblems decrease when recursing
             Δ & (s push ρ₁ for r∈Δ) ⊢ᵣ ρ₁ → -- domain is resolvable
             Δ & s , r∈Δ ⊢ ρ₂ ↓ a → -- codomain matches
             Δ & s , r∈Δ ⊢ ρ₁ ⇒ ρ₂ ↓ a
    i-tabs : ∀ {ρ a r s} {r∈Δ : r List.∈ Δ} b →
             Δ & s , r∈Δ ⊢ ρ tp[/tp b ] ↓ a → Δ & s , r∈Δ ⊢ ∀' ρ ↓ a

  data _&_⊢ᵣ_ {ν} (Δ : ICtx ν) : Stack' Δ → Type ν → Set where
    r-simp : ∀ {r τ s} → (r∈Δ : r List.∈ Δ) → Δ & s , r∈Δ ⊢ r ↓ τ → Δ & s ⊢ᵣ simpl τ
    r-iabs : ∀ {ρ₁ ρ₂} {s : Stack' Δ} → ((ρ₁ List.∷ Δ) & (s prepend ρ₂) ⊢ᵣ ρ₂) →
             Δ & s ⊢ᵣ (ρ₁ ⇒ ρ₂)
    r-tabs : ∀ {ρ s} → ictx-weaken Δ & stack-weaken s ⊢ᵣ ρ → Δ & s ⊢ᵣ ∀' ρ

-- We instantiate the stack with types that act as 'infinity' on the goal.
-- Every possible 'subgoal' we encounter and push to the stack will certainly
-- be smaller than r
_⊢ᵣ_ : ∀ {ν} → ICtx ν → Type ν → Set
Δ ⊢ᵣ r = Δ & All.tabulate (const r) ⊢ᵣ r
