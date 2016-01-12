open import Prelude

module Implicits.Improved.Stack.Decidable (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Coinduction
open import Data.Fin.Substitution
open import Data.List.Any
open Membership-≡
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Substitutions.Lemmas TC _tc≟_
open import Implicits.Improved.Stack.Resolution TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Function.Equality hiding (cong)
open import Data.List.Any.Properties using (Any↔)

module M = MetaTypeMetaSubst

mutual
  {-# NO_TERMINATION_CHECK #-}
  match' : ∀ {m ν} (Δ : ICtx ν) s r∈Δ τ → (r : MetaType m ν) →
          Dec (∃ λ u → Δ & s , r∈Δ ⊢ from-meta (r M./ u) ↓ τ)
  match' Δ s r∈Δ τ (simpl x) with mgu (simpl x) τ 
  match' Δ s r∈Δ τ (simpl x) | just (u , p) =
    yes (
      (asub u) ,
      subst (λ a → Δ & s , r∈Δ  ⊢ a ↓ τ) (sym $ mgu-unifies (simpl x) τ (u , p)) (i-simp τ)
    )
  match' Δ s r∈Δ τ (simpl x) | nothing = no (λ{ (proj₁ , proj₂) → {!!} })

  match' Δ s r∈Δ τ (a ⇒ b) with match' Δ s r∈Δ τ b 
  match' Δ s r∈Δ τ (a ⇒ b) | no ¬p = no {!!}
  match' Δ s r∈Δ τ (a ⇒ b) | yes (u , b/u↓τ) with
    all (λ x → (r∈Δ , (from-meta (a M./ u))) ?⊬dom x) s
  match' Δ s r∈Δ τ (a ⇒ b) | yes (u , b/u↓τ) | yes p
    -- The following with clause fails to satisfy termination checking
    with let a' = from-meta (a M./ u) in resolve' Δ ((r∈Δ , a') List.∷ s) a'
  match' Δ s r∈Δ τ (a ⇒ b) | yes (u , b/u↓τ) | yes p | yes ⊢ᵣa = yes (u , i-iabs p ⊢ᵣa b/u↓τ)
  match' Δ s r∈Δ τ (a ⇒ b) | yes (u , b/u↓τ) | yes p | no ¬⊢ᵣa =
    no (λ{ (u' , i-iabs x ⊢ᵣa a⇒b↓τ) → {!¬⊢ᵣa ⊢ᵣa!} })
  match' Δ s r∈Δ τ (a ⇒ b) | yes (u , b/u↓τ) | no ¬p = no {!!}

  -- The following with clause fails to satisfy termination checking
  match' Δ s r∈Δ τ (∀' a) with match' Δ s r∈Δ τ (open-meta a)
  match' Δ s r∈Δ τ (∀' a) | yes p = yes $ lem p
    where
      lem : (∃ λ u → Δ & s , r∈Δ ⊢ (from-meta ((open-meta a) M./ u)) ↓ τ) →
          ∃ λ u' → Δ & s , r∈Δ ⊢ (from-meta (∀' a M./ u')) ↓ τ
      lem (u ∷ us , p) = us , (i-tabs (from-meta u) (subst (λ v → Δ & s , r∈Δ ⊢ v ↓ τ) (begin
            from-meta (M._/_ (open-meta a) (u ∷ us))
              ≡⟨ cong (λ v → from-meta (M._/_ (open-meta a) v)) (sym $ us↑-⊙-sub-u≡u∷us u us) ⟩
            from-meta ((open-meta a) M./ (us M.↑ M.⊙ (M.sub u)))
              ≡⟨ cong from-meta (/-⊙ (open-meta a)) ⟩
            from-meta ((open-meta a) M./ us M.↑ M./ (M.sub u))
              ≡⟨ lem' a u us ⟩
            from-meta (M._/_ a (us M.↑tp)) tp[/tp from-meta u ] ∎) p))
          where open MetaTypeMetaLemmas hiding (subst)
  match' Δ s r∈Δ τ (∀' r) | no ¬p = no {!!}

  -- match defers to match', which concerns itself with MetaTypes.
  -- If match' finds a match, we can use the fact that we have zero unification variables open here
  -- to show that we found the right thing.
  match : ∀ {ν} (Δ : ICtx ν) s r∈Δ → ∀ r τ → Dec (Δ & s , r∈Δ ⊢ r ↓ τ)
  match Δ s r∈Δ a τ with match' Δ s r∈Δ τ (to-meta {zero} a)
  match Δ s r∈Δ a τ | yes x = yes (lem x)
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
  match Δ s r∈Δ a τ | no ¬p = no {!!}

  match1st : ∀ {ν} (Δ : ICtx ν) s τ  → Dec (Any (λ r → Δ & s , r ⊢ r ↓ τ) Δ)
  match1st Δ s τ = match1st' Δ Δ s τ -- any (λ r → match Δ r τ)
    where
      match1st' : ∀ {ν} (Δ ρs : ICtx ν) s → (τ : SimpleType ν) →
                  Dec (Any (λ r → Δ & s , r ⊢ r ↓ τ) ρs)
      match1st' Δ List.[] s τ = no {!!}
      match1st' Δ (x List.∷ xs) s τ with match Δ s x x τ
      match1st' Δ (x List.∷ xs) s τ | yes px = yes (here px)
      match1st' Δ (x List.∷ xs) s τ | no ¬p with match1st' Δ xs s τ
      match1st' Δ (x List.∷ xs) s τ | no ¬p | yes y = yes (there y)
      match1st' Δ (x List.∷ xs) s τ | no ¬p | no ¬q = no {!!}

  resolve' : ∀ {ν} (Δ : ICtx ν) s r → (Dec (Δ & s ⊢ᵣ r))
  resolve' Δ s (simpl x) with match1st Δ s x
  resolve' Δ s (simpl x) | yes p =
    let r , r∈Δ , r↓x = (Inverse.from Any↔) Π.⟨$⟩ p in yes (r-simp r∈Δ r↓x)
  resolve' Δ s (simpl x) | no ¬p =
    no (λ{ (r-simp x₁ x₂) → ¬p (_⟨$⟩_ (Inverse.to Any↔) (_ , (x₁ , x₂))) })
  resolve' Δ s (a ⇒ b) with resolve' (a List.∷ Δ) s b
  resolve' Δ s (a ⇒ b) | yes p = yes (r-iabs p)
  resolve' Δ s (a ⇒ b) | no ¬p = no (λ{ (r-iabs x) → ¬p x })
  resolve' Δ s (∀' r) with resolve' (ictx-weaken Δ) (stack-weaken s) r
  resolve' Δ s (∀' r) | yes p = yes (r-tabs p)
  resolve' Δ s (∀' r) | no ¬p = no λ{ (r-tabs x) → ¬p x }

  resolve : ∀ {ν} (Δ : ICtx ν) r → (Dec (Δ & List.[] ⊢ᵣ r))
  resolve Δ r = resolve' Δ List.[] r
