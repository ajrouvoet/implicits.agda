open import Prelude

module Implicits.Improved.Finite2.Algorithm (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Induction.WellFounded
open import Induction.Nat
open import Data.Fin.Substitution
open import Data.Nat.Base using (_<′_)
open import Data.List.Any
open Membership-≡
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Substitutions.Lemmas TC _tc≟_
open import Implicits.Improved.Finite2.Resolution TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Function.Equality hiding (cong; flip; const)
open import Data.List.Any.Properties using (Any↔)
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
open import Relation.Binary using (module DecTotalOrder)
open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl)

module M = MetaTypeMetaSubst

module Lemmas where
  postulate lem₄ : ∀ {m ν} (a : MetaType m (suc ν)) u us → from-meta ((M.open-meta a) M./ (us M.↑) M./ (M.sub u)) ≡ (from-meta (a M./ (us M.↑tp))) tp[/tp from-meta u ]

open Lemmas

{-# NO_TERMINATION_CHECK #-}
mutual

  -- Oliveira's termination condition on the implicit context
  Δ⊢term : ∀ {ν} → ICtx ν → Set
  Δ⊢term Δ = All ⊢term Δ

  ⊢term-weaken : ∀ {ν} k {a : Type (k N+ ν)} → ⊢term a →
                  ⊢term (a TypeSubst./ TypeSubst.wk TypeSubst.↑⋆ k)
  ⊢term-weaken k (term-simp {τ}) with TypeLemmas.simpl-wk k τ 
  ⊢term-weaken k (term-simp {τ}) | proj₁ , proj₂ = subst (λ x → ⊢term x) (sym $ proj₂) term-simp
  ⊢term-weaken k (term-all p) = term-all (⊢term-weaken (suc k) p)
  ⊢term-weaken k (term-rule {a = a} {b = b} aT bT x) =
    term-rule (⊢term-weaken k aT) (⊢term-weaken k bT)
      (subst₂ (λ u v → u N< v) (TypeLemmas.||a/wk↑k|| k {!a!}) {!!} x)

  ΔT-weaken : ∀ {ν} {Δ : ICtx ν} → Δ⊢term Δ → Δ⊢term (ictx-weaken Δ)
  ΔT-weaken All.[] = All.[]
  ΔT-weaken (px All.∷ ΔT) = ⊢term-weaken zero px All.∷ ΔT-weaken ΔT

  match' : ∀ {m ν ρ} (Δ : ICtx ν) (ΔT : Δ⊢term Δ) (r∈Δ : ρ List.∈ Δ) τ → (r : MetaType m ν) →
           Maybe (∃ λ u → Δ ⊢ from-meta (r M./ u) ↓ τ)
  match' Δ ΔT r∈Δ τ (simpl x) with mgu (simpl x) τ 
  match' Δ ΔT r∈Δ τ (simpl x) | just (u , p) =
    just (
      (asub u) ,
      subst (λ a → Δ ⊢ a ↓ τ) (sym $ mgu-unifies (simpl x) τ (u , p)) (i-simp τ)
    )
  match' Δ ΔT r∈Δ τ (simpl x) | nothing = nothing

  match' Δ ΔT r∈Δ τ (a ⇒ b) with match' Δ ΔT r∈Δ τ b
  match' Δ ΔT r∈Δ τ (a ⇒ b) | nothing = nothing
  match' Δ ΔT r∈Δ τ (a ⇒ b) | just (u , b/u↓τ) with resolve' Δ ΔT (from-meta (a M./ u))
  match' Δ ΔT r∈Δ τ (a ⇒ b) | just (u , b/u↓τ) | just ⊢ᵣa = just (u , i-iabs ⊢ᵣa b/u↓τ)
  match' Δ ΔT r∈Δ τ (a ⇒ b) | just (u , b/u↓τ) | nothing = nothing

  -- The following with clause fails to satisfy termination checking.
  -- Somehow we have to prove to Agda that (open-meta a) is structurally smaller than (∀' a)
  match' Δ ΔT r∈Δ τ (∀' a) with match' Δ ΔT r∈Δ τ (open-meta a)
  match' Δ ΔT r∈Δ τ (∀' a) | just p = just $ lem p
    where
      lem : (∃ λ u → Δ ⊢ (from-meta ((open-meta a) M./ u)) ↓ τ) →
          ∃ λ u' → Δ ⊢ (from-meta (∀' a M./ u')) ↓ τ
      lem (u ∷ us , p) = us , (i-tabs (from-meta u) (subst (λ v → Δ ⊢ v ↓ τ) (begin
            from-meta (M._/_ (open-meta a) (u ∷ us))
              ≡⟨ cong (λ v → from-meta (M._/_ (open-meta a) v)) (sym $ us↑-⊙-sub-u≡u∷us u us) ⟩
            from-meta ((open-meta a) M./ (us M.↑ M.⊙ (M.sub u)))
              ≡⟨ cong from-meta (/-⊙ (open-meta a)) ⟩
            from-meta ((open-meta a) M./ us M.↑ M./ (M.sub u))
              ≡⟨ lem₄ a u us ⟩
            from-meta (M._/_ a (us M.↑tp)) tp[/tp from-meta u ] ∎) p))
          where open MetaTypeMetaLemmas hiding (subst)
  match' Δ ΔT r∈Δ τ (∀' r) | nothing = nothing

  -- match defers to match', which concerns itself with MetaTypes.
  -- If match' finds a match, we can use the fact that we have zero unification variables open here
  -- to show that we found the right thing.
  match : ∀ {ν ρ} (Δ : ICtx ν) (ΔT : Δ⊢term Δ) (r∈Δ : ρ List.∈ Δ) r τ →
          Maybe (Δ ⊢ r ↓ τ)
  match Δ ΔT r∈Δ a τ with match' Δ ΔT r∈Δ τ (to-meta {zero} a)
  match Δ ΔT r∈Δ a τ | just x = just (lem x)
    where
      eq : ∀ {ν} {a : Type ν} {s} → from-meta (to-meta {zero} a M./ s) ≡ a
      eq {a = a} {s = []} = begin
          from-meta (M._/_ (to-meta {zero} a) [])
          ≡⟨ cong (λ q → from-meta q) (MetaTypeMetaLemmas.id-vanishes (to-meta {zero} a)) ⟩
          from-meta (to-meta {zero} a)
          ≡⟨ to-meta-zero-vanishes ⟩
          a ∎
      lem : ∃ (λ u → Δ ⊢ from-meta (to-meta {zero} a M./ u) ↓ τ) →
                Δ ⊢ a ↓ τ
      lem ([] , proj₂) = subst (λ u → Δ ⊢ u ↓ τ) eq proj₂
  match Δ ΔT r∈Δ a τ | nothing = nothing

  match1st : ∀ {ν} (Δ : ICtx ν) (ΔT : Δ⊢term Δ) τ → 
             Maybe (∃₂ λ r (r∈Δ : r List.∈ Δ) → Δ ⊢ r ↓ τ)
  match1st {ν = ν} Δ ΔT τ = match1st' Δ Prelude.id τ -- any (λ r → match Δ r τ)
    where
      match1st' : ∀ (ρs : ICtx ν) → ρs ⊆ Δ → (τ : SimpleType ν) →
                  Maybe (∃₂ λ r (r∈Δ : r List.∈ Δ) → Δ ⊢ r ↓ τ)
      match1st' List.[] sub τ = nothing
      match1st' (x List.∷ xs) sub τ with match Δ ΔT (sub (here refl)) x τ 
      match1st' (x List.∷ xs) sub τ | just px = just (x , ((sub (here refl)) , px)) 
      match1st' (x List.∷ xs) sub τ | nothing with match1st' xs (λ r∈xs → sub (there r∈xs)) τ 
      match1st' (x List.∷ xs) sub τ | nothing | just p = just p
      match1st' (x List.∷ xs) sub τ | nothing | nothing = nothing

  resolve' : ∀ {ν} (Δ : ICtx ν) (ΔT : Δ⊢term Δ) r → (Maybe (Δ ⊢ᵣ r))
  resolve' Δ ΔT (simpl x) with match1st Δ ΔT x
  resolve' Δ ΔT (simpl x) | just (_ , r∈Δ , r↓x) = just (r-simp r∈Δ r↓x)
  resolve' Δ ΔT (simpl x) | nothing = nothing -- no (λ{ (r-simp x₁ x₂) → ¬p (_⟨$⟩_ (Inverse.to Any↔) (_ , (x₁ , x₂))) })
  resolve' Δ ΔT (a ⇒ b) with resolve' (a List.∷ Δ) {!!} b
  resolve' Δ ΔT (a ⇒ b) | just p = just (r-iabs p)
  resolve' Δ ΔT (a ⇒ b) | nothing = nothing -- no (λ{ (r-iabs x) → ¬p x })
  resolve' Δ ΔT (∀' r) with resolve' (ictx-weaken Δ) {!!} r
  resolve' Δ ΔT (∀' r) | just p = just (r-tabs p)
  resolve' Δ ΔT (∀' r) | nothing = nothing --no (λ{ (r-tabs x) → ¬p x })

  resolve : ∀ {ν} (Δ : ICtx ν) (ΔT : Δ⊢term Δ) r → (Maybe (Δ ⊢ᵣ r))
  resolve Δ ΔT r = resolve' Δ ΔT r
