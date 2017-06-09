module FSub.Intrinsic.Declarative.Semantics where

open import Prelude
open import Data.Product
open import Data.List
open import Data.List.All as All hiding (map)

open import FSub.Types
open import FSub.Intrinsic.Declarative.Syntax

Env : ∀ {n} → νCtx n → Ctx n → Set
data Val {n}(N : νCtx n) : Type n → Set where
  unit : Val {n} N Unit
  clos  : ∀ {a b Γ} → Env N Γ → Term N (Γ +tm a) b → Val N (a ⇒ b)
  tclos : ∀ {a Γ} u → Env N Γ → Term (N +ν u) (Γ +ty) a → Val N (∀≤ u a)

data Val<: {n}(N : νCtx n) : Type n → Set where
  _%_ : ∀ {l a} → Val N l → N ⊢ l <: a → Val<: N a

-- We keep an environment around that has a typing
-- that is *only as-strong* as the preservation theorem we want to prove.
-- This allows us to circumvent the necessity of a narrowing lemma for terms!
Env N Γ = All (λ u → Val<: N u) Γ

open import Data.Star hiding (_>>=_)

module Canonical where

  -- All values upperbounded by some function type, themselves have a function type;
  -- You might expect the lemma to state that the value *is* a closure; but for this you need
  -- heterogeneous equality and (consequently?) the lemma is annoying to prove.
  <:⇒ : ∀ {n N}{a b x : Type n} → Val N x → N ⊢ x <: a ⇒ b → ∃₂ λ a' b' → x ≡ (a' ⇒ b')
  <:⇒ v ε = _ , _ , refl
  <:⇒ () (ν x ◅ p)
  <:⇒ () (Bot<: ◅ _)
  <:⇒ v (_<:Top ◅ p) = ⊥-elim (<:-Lemmas.top-max (λ ()) p)
  <:⇒ v (∀≤ u ◅ p) = ⊥-elim (<:-Lemmas.¬∀≤⇒ p)
  <:⇒ v ((a ⇒ b) ◅ p) = _ , _ , refl

  -- Similar lemma for type closures
  <:∀≤ : ∀ {n N u a}{x : Type n} → Val N x → N ⊢ x <: (∀≤ u a) → ∃₂ λ a' u' → x ≡ (∀≤ u' a')
  <:∀≤ v ε = _ , _ , refl
  <:∀≤ () (ν x ◅ p)
  <:∀≤ () (Bot<: ◅ p)
  <:∀≤ v (_<:Top ◅ p) = ⊥-elim (<:-Lemmas.top-max (λ ()) p)
  <:∀≤ v ((_ ⇒ _) ◅ p) = ⊥-elim (<:-Lemmas.¬⇒≤∀ p)
  <:∀≤ (tclos {a = a} u E t) (∀≤ x ◅ p) = a , u , refl

open import Category.Monad.Partiality
open import Coinduction
open Workaround
open import Data.List.Any
open Membership-≡

open import Data.Vec using ([])

-- We're using a non-strict version of type-preservation to be able to ignore subsumption
-- in the interpreter:
-- A similar note as for the intrinsic+algorithmic version of the semantics holds here:
-- erasing the return type of this sound interpreter is non-trivial.
_⊢_⇓P : ∀ {Γ : Ctx 0}{a} → Env [] Γ → Term [] Γ a → (Val<: [] a) ⊥P
E ⊢ var x ⇓P = now (lookup E x)
E ⊢ unit ⇓P = now (unit % <:-refl)
E ⊢ ƛ a t ⇓P = now (clos E t % <:-refl)
E ⊢ Λ u t ⇓P = now (tclos u E t % <:-refl)
E ⊢ f · e ⇓P = (E ⊢ f ⇓P) >>= λ z → (E ⊢ e ⇓P) >>= λ v → eval-body v z
  where
    eval-body : ∀ {a b} →
                (Val<: [] a) →
                (Val<: [] (a ⇒ b)) →
                (Val<: [] b) ⊥P
    -- we need a lemma `<:⇒` to prove that the all values obtained from evaluating a
    -- term of type "a ⇒ b", must be closures.
    eval-body (v∈l % l-sub) (v∈φ % φ-sub) with Canonical.<:⇒ v∈φ φ-sub
    eval-body (v∈l % l<:a) (clos E t % φ-sub) | _ , _ , refl =
      later (♯ (
        -- First we extend the closure environment with the value obtained from interpreting the argument.
        -- we have to prove that the value's type is a subtype of the function-value's domain.
        -- We need to use the preservation-fact, as well as a lemma stating that functions are
        -- contravariant in their argument type.
        -- Given this environment we can evaluate the body of the closure.
        ((v∈l % (<:-trans l<:a (<:-Lemmas.⇒-contra-dom φ-sub))) ∷ E) ⊢ t ⇓P >>= λ{
          -- Evaluating the body will yield a return value and a subtyping fact.
          -- We use subypting transitivity to prove that this value is a subtype of the
          -- function's return-type.
          (v∈r % r<:b') → now (v∈r % <:-trans r<:b' (<:-Lemmas.⇒-cov-range φ-sub))
      }))
E ⊢ t [ x ] ⇓P = (E ⊢ t ⇓P) >>= {!!}
E ⊢ subm t l<:a ⇓P =
  -- Here we have to use a bind to "coerce" the return type using transitivity.
  -- This should be erased in the derived interpreter.
  (E ⊢ t ⇓P) >>= (λ{ (v∈l' % l'<:l) → now (v∈l' % <:-trans l'<:l l<:a) })