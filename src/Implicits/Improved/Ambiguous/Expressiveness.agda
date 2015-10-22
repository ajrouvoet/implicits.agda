open import Prelude

module Implicits.Improved.Ambiguous.Expressiveness (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Coinduction
open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_

module not-syntax-directed⊇oliveira-ambiguous where

  open import Implicits.Oliveira.Ambiguous.Resolution TC _tc≟_ as A
  open import Implicits.Improved.Ambiguous.Resolution TC _tc≟_
  module I = NotSyntaxDirected
  open I

  p : ∀ {ν n} {a : Type ν} {K : Ktx ν n} → K A.⊢ᵣ a → (proj₂ K) I.⊢ᵣ a
  p (r-tabs x) = r-tabs (♯ (p x))
  p (r-tapp a x) = r-tapp a (♯ (p x))
  p (r-ivar x) = r-ivar x
  p (r-iabs x) = r-iabs (♯ (p x))
  p (r-iapp x y) = r-iapp (♯ (p x)) (♯ p y)


  -- proof that polymorphic id derives every type
  -- this is similar to the non-terminating expression:
  --   x : ∀ {a : Set} → a
  --   x = x
  --
  -- together with ⊇-oliveira-ambiguous, this shows that the coinductive ambiguous rules
  -- are more expressive then the inductive ambiguous rules.
  -- We could easily prove it for simple types, because the empty implicit context
  -- can only build rule types in the inductive case.

  tid : ∀ {n} → Type n
  tid = (∀' (simpl (tvar zero) ⇒ simpl (tvar zero)))

  [tid]⊢a : ∀ {ν} {a : Type ν} → (tid List.∷ List.[]) I.⊢ᵣ a
  [tid]⊢a {a = a} = r-iapp (♯ (r-tapp a (♯ (r-ivar (here refl))))) (♯ [tid]⊢a)

  -- we can even derive it from an empty context, because we can derive identity from nothing:
  []⊢tid : ∀ {ν} → List.[] I.⊢ᵣ tid {ν}
  []⊢tid = r-tabs (♯ (r-iabs (♯ (r-ivar (here refl)))))

  []⊢a : ∀ {ν} {a : Type ν} → List.[] I.⊢ᵣ a
  []⊢a {a} = r-iapp (♯ r-iabs (♯ [tid]⊢a)) (♯ []⊢tid)

module syntax-directed⊇oliveira-deterministic where

  open import Implicits.Oliveira.Deterministic.Resolution TC _tc≟_ as D
  open import Implicits.Improved.Ambiguous.Resolution TC _tc≟_
  module I = SyntaxDirected
  open I

  p : ∀ {ν n} {a : Type ν} {K : Ktx ν n} → K D.⊢ᵣ a → (proj₂ K) I.⊢ᵣ a
  p (r-simp x r↓a) = r-simp (proj₁ $ FirstLemmas.first⟶∈ x) (lem r↓a)
    where
      lem : ∀ {ν n} {K : Ktx ν n} {r a} → K D.⊢ r ↓ a → proj₂ K I.⊢ r ↓ a
      lem (i-simp a) = i-simp a
      lem (i-iabs x₁ x₂) = i-iabs (♯ (p x₁)) (lem x₂)
      lem (i-tabs b x₁) = i-tabs b (lem x₁)
  p (r-iabs ρ₁ x) = r-iabs (p x)
  p (r-tabs x) = r-tabs (p x)

  -- proof that polymorphic id derives every type
  -- this corresponds to the non-terminating expression:
  --   x : ∀ {a : Set} → a
  --   x = x
  --
  -- together with ⊇-oliveira-ambiguous, this shows that the coinductive ambiguous rules
  -- are more expressive then the inductive ambiguous rules.
  -- We could easily prove it for simple types, because the empty implicit context
  -- can only build rule types in the inductive case.

  tid : ∀ {n} → Type n
  tid = (∀' (simpl (tvar zero) ⇒ simpl (tvar zero)))

  tid↓a : ∀ {ν} {a : SimpleType ν} → (tid List.∷ List.[]) I.⊢ tid ↓ a
  tid↓a {a = a} = i-tabs (simpl a) (i-iabs (♯ (r-simp (here refl) tid↓a)) (i-simp a))

  [tid]⊢a : ∀ {ν} {a : Type ν} → (tid List.∷ List.[]) I.⊢ᵣ a
  [tid]⊢a {a = simpl x} = r-simp (here refl) tid↓a
  [tid]⊢a {a = a ⇒ b} = r-iabs (⊆-Δ⊢a [tid]⊢a sub)
    where
      sub : ∀ {a x} → a List.∈ (tid List.∷ List.[]) → a List.∈ (x List.∷ tid List.∷ List.[])
      sub (here px) = there (here px)
      sub (there ())
  [tid]⊢a {a = ∀' a} = r-tabs [tid]⊢a

  -- we can derive identity from nothing:
  []⊢tid : ∀ {ν} → List.[] I.⊢ᵣ tid {ν}
  []⊢tid = r-tabs (r-iabs (r-simp (here refl) (i-simp (tvar zero))))

  -- but interestingly, we CANNOT use this identity, and use it to derive everything else
  -- as in the NotSyntaxDirected resolution rules was possible.
  -- Because we can only apply rules rule types from an empty context.

module SyntaxDirected⊆NotSyntaxDirected where

  open import Implicits.Improved.Ambiguous.Resolution TC _tc≟_
  module A = NotSyntaxDirected
  module S = SyntaxDirected
  open A
  open S

  -- TODO fix
  {-# NO_TERMINATION_CHECK #-}
  thm : ∀ {ν} {Δ : ICtx ν} {a : Type ν} → (Δ S.⊢ᵣ a) → Δ A.⊢ᵣ a
  thm (r-simp r∈Δ r↓a) = lem r↓a (r-ivar r∈Δ)
    where
      lem : ∀ {ν} {Δ : ICtx ν} {r : Type ν} {a : SimpleType ν} →
            Δ S.⊢ r ↓ a → (Δ A.⊢ᵣ r) → (Δ A.⊢ᵣ simpl a)
      lem (i-simp a) q = q
      lem {Δ = Δ} (i-iabs {ρ₁ = ρ₁} x p) q = lem p (r-iapp (♯ q) (♯ (thm (♭ x))))
      lem (i-tabs b p) q = lem p (r-tapp b (♯ q))
  thm (r-iabs x) = r-iabs (♯ (thm x))
  thm (r-tabs x) = r-tabs (♯ (thm x))

  -- the comment in the example above shows that SyntaxDirected is *not* complete wrt the
  -- ambiguous non-syntax-directed rules
