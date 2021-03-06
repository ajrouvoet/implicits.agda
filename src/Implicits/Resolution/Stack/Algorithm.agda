open import Prelude

module Implicits.Resolution.Stack.Algorithm where

open import Induction.WellFounded
open import Induction.Nat
open import Data.Fin.Substitution
open import Data.Nat.Base using (_<′_)
open import Data.List.Any
open Membership-≡
open import Implicits.Syntax
open import Implicits.Substitutions
open import Implicits.Substitutions.Lemmas
open import Implicits.Resolution.Stack.Resolution
open import Implicits.Resolution.Termination
open import Implicits.Syntax.Type.Unification
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

_s<'_ : ∀ {ν} → (∃ λ (Δ : ICtx ν) → Stack Δ) →  (∃ λ (Δ' : ICtx ν) → Stack Δ') → Set
s s<' t = {!!}

module Arg<-well-founded  where
  open Lexicographic (_s<_) (const _sρ<_)

  arg<-well-founded : Well-founded _<_
  arg<-well-founded = well-founded s<-well-founded sρ<-well-founded

  _arg<_ = _<_

open Lexicographic using (left; right)
open Arg<-well-founded

{-# NO_TERMINATION_CHECK #-}
mutual

  match' : ∀ {m ν ρ} (Δ : ICtx ν) s (r∈Δ : ρ List.∈ Δ) τ → (r : MetaType m ν) →
           Acc _arg<_ (s , (, simpl τ)) →
           Acc _m<_ (, , r) →
          Maybe (∃ λ u → Δ & s , r∈Δ ⊢ from-meta (r M./ u) ↓ τ)
  match' Δ s r∈Δ τ (simpl x) (acc f) _ with mgu (simpl x) τ 
  match' Δ s r∈Δ τ (simpl x) (acc f) _ | just (u , p) =
    just (
      (asub u) ,
      subst (λ a → Δ & s , r∈Δ  ⊢ a ↓ τ) (sym $ mgu-unifies (simpl x) τ (u , p)) (i-simp τ)
    )
  match' Δ s r∈Δ τ (simpl x) (acc f) _ | nothing = nothing

  match' Δ s r∈Δ τ (a ⇒ b) (acc f) (acc g) with match' Δ s r∈Δ τ b (acc f) (g _ (b-m<-a⇒b a b))
  match' Δ s r∈Δ τ (a ⇒ b) (acc f) (acc g) | nothing = nothing
  match' Δ s r∈Δ τ (a ⇒ b) (acc f) (acc g) | just (u , b/u↓τ) with
    (from-meta (a M./ u)) for r∈Δ ?⊬dom s
  match' Δ s r∈Δ τ (a ⇒ b) (acc f) (acc g) | just (u , b/u↓τ) | yes p
    with
      let a' = from-meta (a M./ u) in
        let s' = (s push a' for r∈Δ) in
          resolve' Δ s' a' (f (s' , _ , a') (left {!!}))
  match' Δ s r∈Δ τ (a ⇒ b) (acc f) (acc g) | just (u , b/u↓τ) | yes p | just ⊢ᵣa = just (u , i-iabs p ⊢ᵣa b/u↓τ)
  match' Δ s r∈Δ τ (a ⇒ b) (acc f) (acc g) | just (u , b/u↓τ) | yes p | nothing = nothing
  match' Δ s r∈Δ τ (a ⇒ b) (acc f) (acc g) | just (u , b/u↓τ) | no ¬p = nothing

  -- The following with clause fails to satisfy termination checking.
  -- Somehow we have to prove to Agda that (open-meta a) is structurally smaller than (∀' a)
  match' Δ s r∈Δ τ (∀' a) (acc f) (acc g) with
    match' Δ s r∈Δ τ (open-meta a) (acc f) (g _ (open-meta-a-m<-∀'a a))
  match' Δ s r∈Δ τ (∀' a) (acc f) (acc g) | just p = just $ lem p
    where
      lem : (∃ λ u → Δ & s , r∈Δ ⊢ (from-meta ((open-meta a) M./ u)) ↓ τ) →
          ∃ λ u' → Δ & s , r∈Δ ⊢ (from-meta (∀' a M./ u')) ↓ τ
      lem (u ∷ us , p) = us , (i-tabs (from-meta u) (subst (λ v → Δ & s , r∈Δ ⊢ v ↓ τ) (begin
            from-meta (M._/_ (open-meta a) (u ∷ us))
              ≡⟨ cong (λ v → from-meta (M._/_ (open-meta a) v)) (sym $ us↑-⊙-sub-u≡u∷us u us) ⟩
            from-meta ((open-meta a) M./ (us M.↑ M.⊙ (M.sub u)))
              ≡⟨ cong from-meta (/-⊙ (open-meta a)) ⟩
            from-meta ((open-meta a) M./ us M.↑ M./ (M.sub u))
              ≡⟨ lem₄ a u us ⟩
            from-meta (a M./ (us M.↑tp)) tp[/tp from-meta u ] ∎) p))
          where open MetaTypeMetaLemmas hiding (subst)
  match' Δ s r∈Δ τ (∀' r) (acc f) (acc g) | nothing = nothing

  -- match defers to match', which concerns itself with MetaTypes.
  -- If match' finds a match, we can use the fact that we have zero unification variables open here
  -- to show that we found the right thing.
  match : ∀ {ν ρ} (Δ : ICtx ν) s (r∈Δ : ρ List.∈ Δ) r τ → Acc _arg<_ (s , _ , simpl τ) →
          Maybe (Δ & s , r∈Δ ⊢ r ↓ τ)
  match Δ s r∈Δ a τ ac with match' Δ s r∈Δ τ (to-meta {zero} a) ac (m<-well-founded _)
  match Δ s r∈Δ a τ ac | just x = just (lem x)
    where
      eq : ∀ {ν} {a : Type ν} {s} → from-meta (to-meta {zero} a M./ s) ≡ a
      eq {a = a} {s = []} = begin
          from-meta (M._/_ (to-meta {zero} a) [])
          ≡⟨ cong (λ q → from-meta q) (MetaTypeMetaLemmas.id-vanishes (to-meta {zero} a)) ⟩
          from-meta (to-meta {zero} a)
          ≡⟨ to-meta-zero-vanishes ⟩
          a ∎
      lem : ∃ (λ u → Δ & s , r∈Δ ⊢ from-meta (to-meta {zero} a M./ u) ↓ τ) →
                Δ & s , r∈Δ ⊢ a ↓ τ
      lem ([] , proj₂) = subst (λ u → Δ & s , r∈Δ ⊢ u ↓ τ) eq proj₂
  match Δ s r∈Δ a τ ac | nothing = nothing

  match1st : ∀ {ν} (Δ : ICtx ν) (s : Stack Δ) τ → Acc _arg<_ (s , _ , simpl τ) →
             Maybe (∃₂ λ r (r∈Δ : r List.∈ Δ) → Δ & s , r∈Δ ⊢ r ↓ τ)
  match1st Δ s τ ac = match1st' Δ Δ Prelude.id s τ ac -- any (λ r → match Δ r τ)
    where
      match1st' : ∀ {ν} (Δ ρs : ICtx ν) → ρs ⊆ Δ → (s : Stack Δ) → (τ : SimpleType ν) →
                  Acc _arg<_ (s , _ , simpl τ) →
                  Maybe (∃₂ λ r (r∈Δ : r List.∈ Δ) → Δ & s , r∈Δ ⊢ r ↓ τ)
      match1st' Δ List.[] sub s τ ac = nothing
      match1st' Δ (x List.∷ xs) sub s τ ac with match Δ s (sub (here refl)) x τ ac
      match1st' Δ (x List.∷ xs) sub s τ ac | just px = just (x , ((sub (here refl)) , px)) 
      match1st' Δ (x List.∷ xs) sub s τ ac | nothing with
        match1st' Δ xs {!!} s τ ac
      match1st' Δ (x List.∷ xs) sub s τ ac | nothing | just p = just p
      match1st' Δ (x List.∷ xs) sub s τ ac | nothing | nothing = nothing

  resolve' : ∀ {ν} (Δ : ICtx ν) s r → Acc _arg<_ (s , _ , r) → (Maybe (Δ & s ⊢ᵣ r))
  resolve' Δ s (simpl x) ac with match1st Δ s x ac
  resolve' Δ s (simpl x) ac | just (_ , r∈Δ , r↓x) = just (r-simp r∈Δ r↓x)
  resolve' Δ s (simpl x) ac | nothing = nothing
    -- no (λ{ (r-simp x₁ x₂) → ¬p (_⟨$⟩_ (Inverse.to Any↔) (_ , (x₁ , x₂))) })
  resolve' Δ s (a ⇒ b) (acc f) with resolve' (a List.∷ Δ) (s prepend a) b {!f!} 
  resolve' Δ s (a ⇒ b) (acc f) | just p = just (r-iabs p)
  resolve' Δ s (a ⇒ b) (acc f) | nothing = nothing -- no (λ{ (r-iabs x) → ¬p x })
  resolve' Δ s (∀' r) (acc f) with resolve' (ictx-weaken Δ) (stack-weaken s) r {!f ? ?!}
  resolve' Δ s (∀' r) (acc f) | just p = just (r-tabs p)
  resolve' Δ s (∀' r) (acc f) | nothing = nothing --no (λ{ (r-tabs x) → ¬p x })

  resolve : ∀ {ν} (Δ : ICtx ν) r → (Maybe (Δ ⊢ᵣ r))
  resolve Δ r = resolve' Δ (All.tabulate (const r)) r (arg<-well-founded _)
