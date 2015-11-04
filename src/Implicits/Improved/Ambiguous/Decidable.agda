open import Prelude

module Implicits.Improved.Ambiguous.Decidable (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Coinduction
open import Data.Fin.Substitution
open import Data.List.Any
open Membership-≡
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Substitutions.Lemmas TC _tc≟_
open import Implicits.Improved.Ambiguous.Resolution TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Function.Equality hiding (cong)
open import Data.List.Any.Properties using (Any↔)

open SyntaxDirectedFinite

module M = MetaTypeMetaSubst

mutual
    {-# NO_TERMINATION_CHECK #-}
    match' : ∀ {m ν} (Δ : ICtx ν) → (τ : SimpleType ν) → (r : MetaType m ν) →
            Maybe (∃ λ u → Δ ⊢ from-meta (r M./ u) ↓ τ)
    match' Δ τ (simpl x) with mgu (simpl x) τ 
    match' Δ τ (simpl x) | just (u , p) =
      just (
        (asub u) ,
        subst (λ a → Δ ⊢ a ↓ τ) (sym $ mgu-unifies (simpl x) τ (u , p)) (i-simp τ)
      )
    match' Δ τ (simpl x) | nothing = nothing
    match' Δ τ (a ⇒ b) with match' Δ τ b 
    match' Δ τ (a ⇒ b) | nothing = nothing
    match' Δ τ (a ⇒ b) | just (u , b/u↓τ) with (from-meta (a M./ u)) ρ<? (from-meta (b M./ u))
    match' Δ τ (a ⇒ b) | just (u , b/u↓τ) | yes p with resolve Δ (from-meta (a M./ u))
    match' Δ τ (a ⇒ b) | just (u , b/u↓τ) | yes p | just ⊢ᵣa = just (u , i-iabs p ⊢ᵣa b/u↓τ)
    match' Δ τ (a ⇒ b) | just (u , b/u↓τ) | yes p | nothing = nothing
    match' Δ τ (a ⇒ b) | just (u , b/u↓τ) | no ¬p = nothing
    match' Δ τ (∀' a) with match' Δ τ (open-meta a)
    match' Δ τ (∀' a) | just p = just $ lem p
      where
        lem : (∃ λ u → Δ ⊢ (from-meta ((open-meta a) M./ u)) ↓ τ) →
            ∃ λ u' → Δ ⊢ (from-meta (∀' a M./ u')) ↓ τ
        lem (u ∷ us , p) = us , (i-tabs (from-meta u) (subst (λ v → Δ ⊢ v ↓ τ) (begin
              from-meta (M._/_ (open-meta a) (u ∷ us))
                ≡⟨ cong (λ v → from-meta (M._/_ (open-meta a) v)) (sym $ us↑-⊙-sub-u≡u∷us u us) ⟩
              from-meta ((open-meta a) M./ (us M.↑ M.⊙ (M.sub u)))
                ≡⟨ cong from-meta (/-⊙ (open-meta a)) ⟩
              from-meta ((open-meta a) M./ us M.↑ M./ (M.sub u))
                ≡⟨ lem' a u us ⟩
              from-meta (M._/_ a (us M.↑tp)) tp[/tp from-meta u ] ∎) p))
            where open MetaTypeMetaLemmas hiding (subst)
    match' Δ τ (∀' r) | nothing = nothing

    -- match defers to match', which concerns itself with MetaTypes.
    -- If match' finds a match, we can use the fact that we have zero unification variables open here
    -- to show that we found the right thing.
    match : ∀ {ν} (Δ : ICtx ν) → (r : Type ν) → (τ : SimpleType ν) → Maybe (Δ ⊢ r ↓ τ)
    match Δ a τ with match' Δ τ (to-meta {zero} a) -- >>= (λ x → now (lem <$> x))
    match Δ a τ | just x = just (lem x)
      where
        eq : ∀ {ν} {a : Type ν} {s} → from-meta (to-meta {zero} a M./ s) ≡ a
        eq {a = a} {s = []} = begin
            from-meta (M._/_ (to-meta {zero} a) [])
            ≡⟨ cong (λ q → from-meta q) (MetaTypeMetaLemmas.id-vanishes (to-meta {zero} a)) ⟩
            from-meta (to-meta {zero} a)
            ≡⟨ to-meta-zero-vanishes ⟩
            a ∎
        lem : ∃ (λ u → Δ ⊢ from-meta (to-meta {zero} a M./ u) ↓ τ) → Δ ⊢ a ↓ τ
        lem ([] , proj₂) = subst (λ u → Δ ⊢ u ↓ τ) eq proj₂
    match Δ a τ | nothing = nothing

    match1st : ∀ {ν} → (Δ : ICtx ν) → (τ : SimpleType ν) → Maybe (Any (λ r → Δ ⊢ r ↓ τ) Δ)
    match1st Δ τ = match1st' Δ Δ τ -- any (λ r → match Δ r τ)
      where
        match1st' : ∀ {ν} → (Δ ρs : ICtx ν) → (τ : SimpleType ν) → Maybe (Any (λ r → Δ ⊢ r ↓ τ) ρs)
        match1st' Δ List.[] τ = nothing
        match1st' Δ (x List.∷ xs) τ with match Δ x τ
        match1st' Δ (x List.∷ xs) τ | just px = just (here px)
        match1st' Δ (x List.∷ xs) τ | nothing with match1st' Δ xs τ
        match1st' Δ (x List.∷ xs) τ | nothing | just y = just (there y)
        match1st' Δ (x List.∷ xs) τ | nothing | nothing = nothing

    resolve : ∀ {ν} (Δ : ICtx ν) (r : Type ν) → (Maybe (Δ ⊢ᵣ r))
    resolve Δ (simpl x) with match1st Δ x
    resolve Δ (simpl x) | just p =
      let r , r∈Δ , r↓x = (Inverse.from Any↔) Π.⟨$⟩ p in just (r-simp r∈Δ r↓x)
    resolve Δ (simpl x) | nothing = nothing
      -- no (λ{ (r-simp x₁ x₂) → ¬p (_⟨$⟩_ (Inverse.to Any↔) (_ , (x₁ , x₂))) })
    resolve Δ (a ⇒ b) with resolve (a List.∷ Δ) b
    resolve Δ (a ⇒ b) | just p = just (r-iabs p)
    resolve Δ (a ⇒ b) | nothing = nothing -- no (λ{ (r-iabs x) → ¬p x })
    resolve Δ (∀' r) with resolve (ictx-weaken Δ) r
    resolve Δ (∀' r) | just p = just (r-tabs p)
    resolve Δ (∀' r) | nothing = nothing --no (λ{ (r-tabs x) → ¬p x })
