open import Prelude

module Implicits.Improved.Finite.Algorithm (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

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
open import Implicits.Improved.Finite.Resolution TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Function.Equality hiding (cong)
open import Data.List.Any.Properties using (Any↔)
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
open import Relation.Binary using (module DecTotalOrder)
open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl)

module M = MetaTypeMetaSubst

-- let's assume a strict ordering on stacks
postulate _s<_ : ∀ {ν μ} → Stack ν → Stack μ → Set

-- let's assume the ordering is well founded
postulate s<-well-founded : ∀ {ν} → Well-founded (_s<_ {ν})

-- let's have a strict size measure on types
s||_|| : ∀ {ν} → Type ν → ℕ
s|| simpl (tc x) || = 1
s|| simpl (tvar n) || = 1
s|| simpl (a →' b) || = suc (s|| a || N+ s|| b ||)
s|| a ⇒ b || = suc (s|| a || N+ s|| b ||)
s|| ∀' a || = 1 N+ s|| a ||

-- ... and metatypes
m||_|| : ∀ {m ν} → MetaType m ν → ℕ
m|| simpl (tc x) || = 1
m|| simpl (tvar n) || = 1
m|| simpl (mvar n) || = 1
m|| simpl (a →' b) || = suc (m|| a || N+ m|| b ||)
m|| a ⇒ b || = suc (m|| a || N+ m|| b ||)
m|| ∀' a || = 1 N+ m|| a ||

_sρ<_ : ∃ Type → ∃ Type → Set
(_ , a) sρ< (_ , b) = s|| a || N< s|| b ||

_m<_ : ∃₂ MetaType → ∃₂ MetaType → Set
(_ , _ , a) m< (_ , _ , b) = m|| a || N< m|| b ||

-- we can show that our strict size measure a ρ< b is well founded
-- by relating it to the well-foundedness proof of _<'_
sρ<-well-founded : Well-founded _sρ<_
sρ<-well-founded = sub.well-founded (image.well-founded <-well-founded)
  where
    module sub = Inverse-image (λ{ (_ , a) → s|| a ||})
    module image = Subrelation {A = ℕ} {_N<_} {_<′_} ≤⇒≤′

m<-well-founded : Well-founded _m<_
m<-well-founded = sub.well-founded (image.well-founded <-well-founded)
  where
    module sub = Inverse-image (λ{ (_ , _ , a) → m|| a ||})
    module image = Subrelation {A = ℕ} {_N<_} {_<′_} ≤⇒≤′

a-sρ<-∀a : ∀ {n a} → (suc n , a) sρ< (, ∀' a)
a-sρ<-∀a = ≤-refl

b-sρ<-a⇒b : ∀ {ν} (a b : Type ν) → (_ , b) sρ< (_ , a ⇒ b)
b-sρ<-a⇒b a b = s≤s (≤-steps s|| a || ≤-refl)

a-m<-∀a : ∀ {m ν} a → (m , suc ν , a) m< (m , ν , ∀' a)
a-m<-∀a a = ≤-refl 

b-m<-a⇒b : ∀ {m ν} a b → (m , ν , b) m< (m , ν , a ⇒ b)
b-m<-a⇒b a b = s≤s (≤-steps m|| a || ≤-refl)

||open-meta-a||≡a : ∀ {m ν} (a : MetaType m (suc ν)) → m|| open-meta a || ≡ m|| a ||
||open-meta-a||≡a (a ⇒ b) =
  cong₂
    (λ u v → 1 N+ u N+ v)
    (||open-meta-a||≡a a)
    (||open-meta-a||≡a b)
||open-meta-a||≡a (∀' a) = cong (λ u → 1 N+ u) {!!}
||open-meta-a||≡a (simpl (tvar x)) = {!!}
||open-meta-a||≡a (simpl (mvar x)) = refl
||open-meta-a||≡a (simpl (a →' b)) =
  cong₂
    (λ u v → 1 N+ u N+ v)
    (||open-meta-a||≡a a)
    (||open-meta-a||≡a b)
||open-meta-a||≡a (simpl (tc c)) = refl

open-meta-a-m<-∀'a : ∀ {m ν} a → (suc m , ν , open-meta a) m< (m , ν , ∀' a)
open-meta-a-m<-∀'a a = subst (λ x → x N< m||  ∀' a ||) (sym $ ||open-meta-a||≡a a) (a-m<-∀a a)

module Arg<-well-founded {ν : ℕ} where
  open Lexicographic (_s<_ {ν}) (λ x → _sρ<_)

  arg<-well-founded : Well-founded _<_
  arg<-well-founded = well-founded s<-well-founded sρ<-well-founded

  _arg<_ = _<_

open Lexicographic using (left; right)
open Arg<-well-founded

mutual
  match' : ∀ {m ν} (Δ : ICtx ν) s r∈Δ τ → (r : MetaType m ν) →
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
    all (λ x → (r∈Δ , (from-meta (a M./ u))) ?⊬dom x) s
  match' Δ s r∈Δ τ (a ⇒ b) (acc f) (acc g) | just (u , b/u↓τ) | yes p
    with let a' = from-meta (a M./ u) in
      resolve' Δ ((r∈Δ , a') List.∷ s) a' (f (((r∈Δ , a') List.∷ s) , , a') (left {!!}))
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
              ≡⟨ lem' a u us ⟩
            from-meta (M._/_ a (us M.↑tp)) tp[/tp from-meta u ] ∎) p))
          where open MetaTypeMetaLemmas hiding (subst)
  match' Δ s r∈Δ τ (∀' r) (acc f) (acc g) | nothing = nothing

  -- match defers to match', which concerns itself with MetaTypes.
  -- If match' finds a match, we can use the fact that we have zero unification variables open here
  -- to show that we found the right thing.
  match : ∀ {ν} (Δ : ICtx ν) s r∈Δ r τ → Acc _arg<_ (s , _ , simpl τ) → Maybe (Δ & s , r∈Δ ⊢ r ↓ τ)
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

  match1st : ∀ {ν} (Δ : ICtx ν) s τ → Acc _arg<_ (s , _ , simpl τ) → Maybe (Any (λ r → Δ & s , r ⊢ r ↓ τ) Δ)
  match1st Δ s τ ac = match1st' Δ Δ s τ ac -- any (λ r → match Δ r τ)
    where
      match1st' : ∀ {ν} (Δ ρs : ICtx ν) s → (τ : SimpleType ν) → Acc _arg<_ (s , _ , simpl τ) →
                  Maybe (Any (λ r → Δ & s , r ⊢ r ↓ τ) ρs)
      match1st' Δ List.[] s τ ac = nothing
      match1st' Δ (x List.∷ xs) s τ ac with match Δ s x x τ ac
      match1st' Δ (x List.∷ xs) s τ ac | just px = just (here px)
      match1st' Δ (x List.∷ xs) s τ ac | nothing with match1st' Δ xs s τ ac
      match1st' Δ (x List.∷ xs) s τ ac | nothing | just y = just (there y)
      match1st' Δ (x List.∷ xs) s τ ac | nothing | nothing = nothing

  resolve' : ∀ {ν} (Δ : ICtx ν) s r → Acc _arg<_ (s , _ , r) → (Maybe (Δ & s ⊢ᵣ r))
  resolve' Δ s (simpl x) ac with match1st Δ s x ac
  resolve' Δ s (simpl x) ac | just p =
    let r , r∈Δ , r↓x = (Inverse.from Any↔) Π.⟨$⟩ p in just (r-simp r∈Δ r↓x)
  resolve' Δ s (simpl x) ac | nothing = nothing
    -- no (λ{ (r-simp x₁ x₂) → ¬p (_⟨$⟩_ (Inverse.to Any↔) (_ , (x₁ , x₂))) })
  resolve' Δ s (a ⇒ b) (acc f) with resolve' (a List.∷ Δ) s b (f (s , _ , b) (right (b-sρ<-a⇒b a b)))
  resolve' Δ s (a ⇒ b) (acc f) | just p = just (r-iabs p)
  resolve' Δ s (a ⇒ b) (acc f) | nothing = nothing -- no (λ{ (r-iabs x) → ¬p x })
  resolve' Δ s (∀' r) (acc f) with resolve' (ictx-weaken Δ) (stack-weaken s) r {!f ? ?!}
  resolve' Δ s (∀' r) (acc f) | just p = just (r-tabs p)
  resolve' Δ s (∀' r) (acc f) | nothing = nothing --no (λ{ (r-tabs x) → ¬p x })

  resolve : ∀ {ν} (Δ : ICtx ν) r → (Maybe (Δ & List.[] ⊢ᵣ r))
  resolve Δ r = resolve' Δ List.[] r (arg<-well-founded (List.[] , _ , r))
