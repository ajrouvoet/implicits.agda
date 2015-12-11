open import Prelude

module Implicits.Improved.Finite3.Algorithm (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

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
open import Implicits.Improved.Finite.Termination TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Function.Equality hiding (cong; flip; const)
open import Data.List.Any.Properties using (Any↔)
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
open import Relation.Binary using (module DecTotalOrder)
open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl)
open Lexicographic using (left; right)

module M = MetaTypeMetaSubst

module Lemmas where
  postulate lem₄ : ∀ {m ν} (a : MetaType m (suc ν)) u us → from-meta ((M.open-meta a) M./ (us M.↑) M./ (M.sub u)) ≡ (from-meta (a M./ (us M.↑tp))) tp[/tp from-meta u ]

  m<-Acc : ∀ {m ν} → MetaType m ν → Set
  m<-Acc {m} {ν} r = Acc _m<_ (m , ν , r)

  ρ<-Acc : ∀ {ν} → Type ν → Set
  ρ<-Acc {ν} r = Acc _ρ<_ (ν , r)

  module Arg<-well-founded  where
    open Lexicographic (_N<_) (const _ρ<_)

    open import Induction.Nat
    open import Data.Nat.Properties
    module image = Subrelation {A = ℕ} {_N<_} {_<′_} ≤⇒≤′

    arg<-well-founded : Well-founded _<_
    arg<-well-founded = well-founded (image.well-founded <-well-founded) ρ<-well-founded

    _arg<_ = _<_

    -- Accessibility of the 'goal' type during resolution.
    -- Either the *head* of the goal shrinks (Oliveira's termination condition)
    -- Or the head size remains equal and the goal shrinks in an absolute sense.
    Arg<-Acc : ∀ {ν} → Type ν → Set
    Arg<-Acc a = Acc _arg<_ (h|| a || , (, a))

  open Arg<-well-founded using (Arg<-Acc; arg<-well-founded) public

open Lemmas

mutual

  match' : ∀ {m ν ρ} (Δ : ICtx ν) (r∈Δ : ρ List.∈ Δ) τ → (r : MetaType m ν) →
           Arg<-Acc (simpl τ) →
           m<-Acc r →
           Maybe (∃ λ u → Δ ⊢ from-meta (r M./ u) ↓ τ)
  match' Δ r∈Δ τ (simpl x) f g with mgu (simpl x) τ 
  match' Δ r∈Δ τ (simpl x) f g | just (u , p) =
    just (
      (asub u) ,
      subst (λ a → Δ ⊢ a ↓ τ) (sym $ mgu-unifies (simpl x) τ (u , p)) (i-simp τ))
  match' Δ r∈Δ τ (simpl x) f g | nothing = nothing

  match' Δ r∈Δ τ (a ⇒ b) (acc f) (acc g) with match' Δ r∈Δ τ b (acc f) (g _ (b-m<-a⇒b a b))
  match' Δ r∈Δ τ (a ⇒ b) (acc f) (acc g) | nothing = nothing
  match' Δ r∈Δ τ (a ⇒ b) (acc f) (acc g) | just (u , b/u↓τ)
    with (from-meta (a M./ u)) hρ<? (simpl τ)
  match' Δ r∈Δ τ (a ⇒ b) (acc f) (acc g) | just (u , b/u↓τ) | yes p
    with resolve' Δ (from-meta (a M./ u)) (f _ (left p))
  match' Δ r∈Δ τ (a ⇒ b) (acc f) (acc g) | just (u , b/u↓τ) | yes _ | just ⊢ᵣa =
    just (u , i-iabs ⊢ᵣa b/u↓τ)
  match' Δ r∈Δ τ (a ⇒ b) (acc f) (acc g) | just (u , b/u↓τ) | yes _ | nothing = nothing
  match' Δ r∈Δ τ (a ⇒ b) (acc f) (acc g) | just (u , b/u↓τ) | no p = nothing

  match' Δ r∈Δ τ (∀' a) f (acc g) with match' Δ r∈Δ τ (open-meta a) f (g _ (open-meta-a-m<-∀'a a))
  match' Δ r∈Δ τ (∀' a) f (acc g) | just p = just $ lem p
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
  match' Δ r∈Δ τ (∀' r) f (acc g) | nothing = nothing

  -- match defers to match', which concerns itself with MetaTypes.
  -- If match' finds a match, we can use the fact that we have zero unification variables open here
  -- to show that we found the right thing.
  match : ∀ {ν ρ} (Δ : ICtx ν) (r∈Δ : ρ List.∈ Δ) r τ → Arg<-Acc (simpl τ) → Maybe (Δ ⊢ r ↓ τ)
  match Δ r∈Δ a τ f with match' Δ r∈Δ τ (to-meta {zero} a) f (m<-well-founded _)
  match Δ r∈Δ a τ f | just x = just (lem x)
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
  match Δ r∈Δ a τ f | nothing = nothing

  match1st : ∀ {ν} (Δ : ICtx ν) τ → Arg<-Acc (simpl τ) →
             Maybe (∃₂ λ r (r∈Δ : r List.∈ Δ) → Δ ⊢ r ↓ τ)
  match1st {ν = ν} Δ τ f = match1st' Δ Prelude.id
    where
      match1st' : ∀ (ρs : ICtx ν) → ρs ⊆ Δ → Maybe (∃₂ λ r (r∈Δ : r List.∈ Δ) → Δ ⊢ r ↓ τ)
      match1st' List.[] sub = nothing
      match1st' (x List.∷ xs) sub with match Δ (sub (here refl)) x τ f
      match1st' (x List.∷ xs) sub | just px = just (x , ((sub (here refl)) , px)) 
      match1st' (x List.∷ xs) sub | nothing with match1st' xs (λ r∈xs → sub (there r∈xs))
      match1st' (x List.∷ xs) sub | nothing | just p = just p
      match1st' (x List.∷ xs) sub | nothing | nothing = nothing

  resolve' : ∀ {ν} (Δ : ICtx ν) r → Arg<-Acc r → (Maybe (Δ ⊢ᵣ r))
  resolve' Δ (simpl x) f with match1st Δ x f
  resolve' Δ (simpl x) f | just (_ , r∈Δ , r↓x) = just (r-simp r∈Δ r↓x)
  resolve' Δ (simpl x) f | nothing = nothing
  resolve' Δ (a ⇒ b) (acc f) with resolve' (a List.∷ Δ) b (f _ (right (b-ρ<-a⇒b a b)))
  resolve' Δ (a ⇒ b) (acc f) | just p = just (r-iabs p)
  resolve' Δ (a ⇒ b) (acc f) | nothing = nothing
  resolve' Δ (∀' r) (acc f) with resolve' (ictx-weaken Δ) r (f _ (right (a-ρ<-∀a r)))
  resolve' Δ (∀' r) (acc f) | just p = just (r-tabs p)
  resolve' Δ (∀' r) (acc f) | nothing = nothing

  resolve : ∀ {ν} (Δ : ICtx ν) r → (Maybe (Δ ⊢ᵣ r))
  resolve Δ r = resolve' Δ r (arg<-well-founded _)
