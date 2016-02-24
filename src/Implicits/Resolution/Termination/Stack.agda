open import Prelude

module Implicits.Resolution.Termination.Stack
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

-- on the stack we maintain, for each rule in Δ,
-- the last goal type that resulted from using the rule
Stack : ∀ {ν} → ICtx ν → Set
Stack {ν} Δ = All (const $ Type ν) Δ

----------------------------------------------------------------
-- basic stack operations

_push_for_ : ∀ {ν r} {Δ : ICtx ν} → Stack Δ → Type ν → r List.∈ Δ → Stack Δ
(a All.∷ s) push a' for here _ = a' All.∷ s
(b All.∷ s) push a for there r∈Δ = b All.∷ s push a for r∈Δ

_prepend_ : ∀ {ν r} {Δ : ICtx ν} → Stack Δ → Type ν → Stack (r List.∷ Δ)
s prepend a = a All.∷ s

_get_ : ∀ {ν r} {Δ : ICtx ν} → Stack Δ → r List.∈ Δ → Type ν
(a All.∷ s) get here _ = a 
(a All.∷ s) get there r∈Δ = s get r∈Δ

ssum : ∀ {ν} {Δ : ICtx ν} → Stack Δ → ℕ
ssum All.[] = 0
ssum (a All.∷ s) = h|| a || N+ ssum s

stack-weaken : ∀ {ν} {Δ : ICtx ν} → Stack Δ → Stack (ictx-weaken Δ)
stack-weaken All.[] = All.[]
stack-weaken (px All.∷ s) = (tp-weaken px) All.∷ (stack-weaken s)

----------------------------------------------------------------
-- stack ordering

_s<_ : ∀ {ν} {Δ : ICtx ν} → (s s' : Stack Δ) → Set
s s< s' = ssum s N< ssum s'

_for_⊬dom_ : ∀ {ν r} {Δ : ICtx ν} → Type ν → r List.∈ Δ → Stack Δ → Set
a for r∈Δ ⊬dom s = (s push a for r∈Δ) s< s
