module FSub.Extrinsic.Declarative.Properties.Sound where

open import Prelude hiding (⊥; id)
open import Function as Fun using ()
open import Data.List hiding ([_]; monad)
open import Data.List.Properties as ListProp using ()
open import Data.Fin.Substitution
open import Extensions.List
open import Data.Maybe hiding (monad)

open import FSub.Types
open import FSub.Extrinsic.Declarative.Welltyped
open import FSub.Extrinsic.Declarative.Semantics

open import Data.Star hiding (_>>=_)

module FunctionalOk where
  open Functional

  -- use transitivity of subtyping as subsumption for values in the
  -- interpreter monad
  trans-ok : ∀ {n}{N : νCtx n}{x a aᵘ} →
            All (Any (λ v → N ⊢̬ v <: a)) x → N ⊢ a <: aᵘ →
            All (Any (λ v → N ⊢̬ v <: aᵘ)) x
  trans-ok (just² v<:a) q = just² {!!}
  trans-ok nothing q = nothing

  _⊢_⇓_ok : ∀ {n N}{Γ : Ctx n}{μ : Env}{t a} →
            N , Γ ⊢ μ → N , Γ ⊢ t ∶ a → ∀ n →
            ------------------------------------------------------------
            All (Any (λ v → N ⊢̬ v <: a)) (μ ⊢ t ⇓ n)

  E ⊢ t ⇓ zero ok = nothing

  E ⊢ unit ⇓ suc n ok = just² (unit % ε)
  E ⊢ ƛ a t ⇓ suc n ok = just² (clos t E % ε)
  E ⊢ Λ u t ⇓ suc n ok = just² (tclos u E t % ε)

  E ⊢ var x ⇓ suc n ok with pointwise-maybe-lookup E x
  ... | _ , is-just , p rewrite is-just = just² p

  E ⊢ f · e ⇓ suc n ok
    with μ ⊢ (eraseᵗᵐ f) ⇓ n | μ ⊢ (eraseᵗᵐ e) ⇓ n | E ⊢ f ⇓ n ok | E ⊢ e ⇓ n ok
    where μ = (eraseᴱ E)
  -- errors
  ... | nothing | _ | x | y = nothing
  ... | just _ | nothing | x | y = nothing
  ... | just nothing | _ | (just ()) | _
  ... | just (just _) | (just nothing) | _ | (just ())
  -- success
  ... | just² x | just² y | just² (v∈l % l<:a⇒b) | just² (v∈k % k<:a) with Canonical.<:⇒ v∈l l<:a⇒b
  E ⊢ f · e ⇓ suc n ok | just² _ | just² _ | just² (clos t Eclos % l<:a⇒b) | just² (v∈k % k<:a) | _ , _ , refl =
    trans-ok
      (((v∈k % <:-trans k<:a (<:-Lemmas.⇒-contra-dom l<:a⇒b)) ∷ Eclos) ⊢ t ⇓ n ok)
      (<:-Lemmas.⇒-cov-range l<:a⇒b)

  E ⊢ t [ x ] ⇓ suc n ok with (eraseᴱ E) ⊢ (eraseᵗᵐ t) ⇓ n | E ⊢ t ⇓ n ok
  ... | nothing | _ = nothing
  ... | just nothing | just ()
  ... | just² _ | just² (v∈l % l<:∀a) with Canonical.<:∀≤ v∈l l<:∀a
  E ⊢ t [ x ] ⇓ suc n ok | just² _ | just² (tclos u body Eclos % l<:∀) | _ , _ , refl = {!!}

  E ⊢ subm t s ⇓ suc n ok = trans-ok (E ⊢ t ⇓ (suc n) ok) s

module RelationalOk where
  open Relational

  functional : ∀ {μ f v v'} → μ ⊢ f ⇓ v → μ ⊢ f ⇓ v' → v ≡ v'
  functional unit⇓ unit⇓ = refl
  functional λ⇓ λ⇓ = refl
  functional Λ⇓ Λ⇓ = refl
  functional (t[]⇓ f b) (t[]⇓ f' b') with functional f f'
  ... | refl with functional b b'
  ... | refl = refl
  functional (var⇓ x) (var⇓ x') rewrite []=-functional _ _ x x' = refl
  functional (app⇓ f e b) (app⇓ f' e' b') with functional f f' | functional e e'
  ... | refl | refl with functional b b'
  ... | refl = refl

  algorithmic : ∀ {μ : Env}{t v} → (l r : μ ⊢ t ⇓ v) → l ≡ r
  algorithmic unit⇓ unit⇓ = refl
  algorithmic λ⇓ λ⇓ = refl
  algorithmic Λ⇓ Λ⇓ = refl
  algorithmic (app⇓ f e b) (app⇓ f' e' b') with functional f f' | functional e e'
  ... | refl | refl with  functional b b' | algorithmic f f' | algorithmic e e'
  ... | refl | refl | refl with algorithmic b b'
  ... | refl = refl
  algorithmic (t[]⇓ f b) (t[]⇓ f' b') with functional f f'
  ... | refl with functional b b' | algorithmic f f'
  ... | refl | refl with algorithmic b b'
  ... | refl = refl
  algorithmic (var⇓ x) (var⇓ x') with []=-algorithmic x x'
  ... | refl = refl

  preservation : ∀ {n N}{Γ : Ctx n}{μ : Env}{t a v} → N , Γ ⊢ μ → N , Γ ⊢ t ∶ a → μ ⊢ t ⇓ v →
                 N ⊢̬ v <: a
  preservation E unit unit⇓ = unit % ε
  preservation E (ƛ a p) λ⇓ = clos p E % ε
  preservation E (Λ u p) Λ⇓ = tclos u E p % ε
  preservation E (f · e) (app⇓ f⇓clos e⇓v body⇓) with preservation E f f⇓clos | preservation E e e⇓v
  ... | clos body Eclos % sub | ev % v<: with
    preservation ((ev % <:-trans v<: (<:-Lemmas.⇒-contra-dom sub)) ∷ Eclos) body body⇓
  ... | r % r<: = r % <:-trans r<: (<:-Lemmas.⇒-cov-range sub)
  preservation E (p [ b ]) (t[]⇓ p⇓tclos body⇓) with preservation E p p⇓tclos
  ... | tclos u Eclos body % sub = {!!}
  preservation E (var p) (var⇓ q) = pointwise-lookup′ E p q
  preservation E (subm p s) subm⇓ with preservation E p subm⇓
  ... | v % v<: = v % <:-trans v<: s

  open import Coinduction
  open import Category.Monad.Partiality
  open Workaround

  sound : ∀ {n N}{Γ : Ctx n}{μ : Env}{t a} →
          N , Γ ⊢ μ → N , Γ ⊢ t ∶ a → (∃ λ v → μ ⊢ t ⇓ v) ⊥P
  sound E unit = now (unit , unit⇓)
  sound E (ƛ a p) = now (clos _ _ , λ⇓)
  sound E (Λ u p) = now (tclos _ _ , Λ⇓)
  sound E (var x) with pointwise-lookup E x
  ... | v , p , v∶a = now (v , var⇓ p)
  sound {N = N} {Γ = Γ} {μ = μ} E (f · e) = sound E f >>= (
    λ fv → sound E e >>= (
    λ v →
      eval-body f (proj₂ fv) e (proj₂ v)
    ))
    where
      eval-body : ∀ {a b f e fv v} →
        N , Γ ⊢ f ∶ (a ⇒ b) → μ ⊢ f ⇓ fv →
        N , Γ ⊢ e ∶ a → μ ⊢ e ⇓ v →
        (∃ λ r → μ ⊢ f · e ⇓ r) ⊥P
      eval-body f f⇓ e e⇓ with preservation E f f⇓ | preservation E e e⇓
      eval-body f f⇓ e e⇓ | fv % s₁ | wtv with Canonical.<:⇒ fv s₁
      eval-body f₁ f⇓ e₁ e⇓ | clos body Eclos % s₁ | wtv % s₂ | (_ , _ , refl) =
        later (♯ (
          (sound ((wtv % (<:-trans s₂ (<:-Lemmas.⇒-contra-dom s₁))) ∷ Eclos) body) >>=
            λ{(r , body⇓) → now (r , app⇓ f⇓ e⇓ body⇓)}
          ))
  sound E (p [ x ]) = {!!}
  sound E (subm p x) = sound E p
