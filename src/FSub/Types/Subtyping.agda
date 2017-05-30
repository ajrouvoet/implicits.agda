module FSub.Types.Subtyping where

open import Prelude
open import FSub.Types
open import Data.Vec

module Declarative where

  -- algorithmic subtyping a la kernel F<:
  open import Data.Star
  mutual
    infixl 5 _⊢_<:₁_
    infixl 5 _⊢_<:_
    data _⊢_<:₁_ {n}(N : νCtx n) : Type n → Type n → Set where
      ν : ∀ {i u} → N [ i ]= u → N ⊢ ν i <:₁ u
      _<:Top : ∀ {a} → N ⊢ a <:₁ Top
      Bot<: : ∀ {a} → N ⊢ Bot <:₁ a
      _⇒_ : ∀ {a a' b b'} → N ⊢ a <: a' → N ⊢ b <: b' → N ⊢ a' ⇒ b <:₁ a ⇒ b'
      ∀≤ : ∀ {u a b} → (N +ν u) ⊢ a <: b → N ⊢ ∀≤ u a <:₁ ∀≤ u b

    -- reflexive, transitive closure of subtyping relation
    _⊢_<:_ : ∀ {n}(N : νCtx n) → Type n → Type n → Set
    N ⊢ a <: b = Star (_⊢_<:₁_ N) a b

  <:-refl : ∀ {n}{N : νCtx n}{a} → N ⊢ a <: a
  <:-refl = ε

  <:-trans = _◅◅_

  module <:-Lemmas where
    top-max : ∀ {n N}{x : Type n} → x ≢ Top → ¬ (N ⊢ Top <: x)
    top-max ¬Top ε = ¬Top refl
    top-max ¬Top (_<:Top ◅ p) = top-max ¬Top p

    ¬∀≤⇒ : ∀ {n N u x}{a b : Type n} → ¬ (N ⊢ ∀≤ u x <: (a ⇒ b))
    ¬∀≤⇒ (_<:Top ◅ p) = top-max (λ ()) p
    ¬∀≤⇒ (∀≤ _ ◅ p) = ¬∀≤⇒ p

    ¬⇒≤∀ : ∀ {n N u x}{a b : Type n} → ¬ (N ⊢ (a ⇒ b) <: ∀≤ u x)
    ¬⇒≤∀ (_<:Top ◅ p) = top-max (λ ()) p
    ¬⇒≤∀ ((_ ⇒ _) ◅ p) = ¬⇒≤∀ p

    ⇒-cov-range : ∀ {n N}{a b aₗ bᵘ : Type n} → N ⊢ (a ⇒ b) <: (aₗ ⇒ bᵘ) → N ⊢ b <: bᵘ
    ⇒-cov-range ε = ε
    ⇒-cov-range (_<:Top ◅ p) = ⊥-elim (top-max (λ ()) p)
    ⇒-cov-range ((a ⇒ b) ◅ p) = <:-trans b (⇒-cov-range p)

    ⇒-contra-dom : ∀ {n N}{a b aₗ bᵘ : Type n} → N ⊢ (a ⇒ b) <: (aₗ ⇒ bᵘ) → N ⊢ aₗ <: a
    ⇒-contra-dom ε = ε
    ⇒-contra-dom (_<:Top ◅ p) = ⊥-elim (top-max (λ ()) p)
    ⇒-contra-dom ((a ⇒ b) ◅ p) = <:-trans (⇒-contra-dom p) a

module Algorithmic where

  -- algorithmic subtyping a la kernel F<:
  infixl 5 _⊢_<:_
  data _⊢_<:_ {n}(N : νCtx n) : Type n → Type n → Set where
    Unit-refl : N ⊢ Unit <: Unit
    ν-refl : ∀ {i} → N ⊢ ν i <: ν i
    ν-trans : ∀ {i u u'} → N [ i ]= u → N ⊢ u <: u' → N ⊢ ν i <: u'

    -- top and bottom of the lattice
    _<:Top : ∀ {a} → N ⊢ a <: Top
    Bot<: : ∀ {a} → N ⊢ Bot <: a

    _⇒_ : ∀ {a a' b b'} → N ⊢ a <: a' → N ⊢ b <: b' → N ⊢ a' ⇒ b <: a ⇒ b'
    ∀≤ : ∀ {u a b} → (N +ν u) ⊢ a <: b → N ⊢ ∀≤ u a <: ∀≤ u b

  -- reflexivity as a theorem
  <:-refl : ∀ {n N}{a : Type n} → N ⊢ a <: a
  <:-refl {a = Top} = _<:Top
  <:-refl {a = Bot} = Bot<:
  <:-refl {a = Unit} = Unit-refl
  <:-refl {a = a ⇒ b} = <:-refl ⇒ <:-refl
  <:-refl {N = N} {a = ν i} = ν-refl
  <:-refl {a = ∀≤ u a} = ∀≤ <:-refl

  -- transitivity as a theorem
  <:-trans : ∀ {n N}{a b c : Type n} → N ⊢ a <: b → N ⊢ b <: c → N ⊢ a <: c
  <:-trans Unit-refl Unit-refl = Unit-refl
  <:-trans ν-refl ν-refl = ν-refl
  <:-trans (ν-trans x p) tail = ν-trans x (<:-trans p tail)
  <:-trans _ _<:Top = _<:Top
  <:-trans Bot<: _ = Bot<:
  <:-trans ν-refl (ν-trans x q) = ν-trans x q
  <:-trans (a ⇒ b) (a' ⇒ b') = (<:-trans a' a) ⇒ (<:-trans b b')
  <:-trans (∀≤ p) (∀≤ q) = ∀≤ (<:-trans p q)

  -- exposure of a type through a type variable (pg. 418 TAPL)
  data _⊢_⇑_ {n}(N : νCtx n) : Type n → Type n → Set where

    -- bottom of the exposure algorithm
    Unit-exp : N ⊢ Unit ⇑ Unit
    Top-exp : N ⊢ Top ⇑ Top
    Bot-exp : N ⊢ Bot ⇑ Bot
    ⇒-exp : ∀ {a b} → N ⊢ (a ⇒ b) ⇑ (a ⇒ b)
    ∀-exp : ∀ {u a} → N ⊢ (∀≤ u a) ⇑ (∀≤ u a)

    -- exposing the structure of a type through the νCtx
    ν : ∀ {i u v} → N [ i ]= u → N ⊢ u ⇑ v → N ⊢ ν i ⇑ v
