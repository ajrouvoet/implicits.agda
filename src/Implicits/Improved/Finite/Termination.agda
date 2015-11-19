open import Prelude

module Implicits.Improved.Finite.Termination (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Induction.WellFounded
open import Induction.Nat
open import Data.Fin.Substitution
open import Data.Nat.Base using (_<′_)
open import Data.List.Any hiding (map)
open Membership-≡
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Substitutions.Lemmas TC _tc≟_
open import Implicits.Improved.Finite.Resolution TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Function.Equality hiding (cong; flip; const)
open import Data.List.Any.Properties using (Any↔)
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
open import Relation.Binary using (module DecTotalOrder)
open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl)

-- type measure on metatypes
m||_|| : ∀ {m ν} → MetaType m ν → ℕ
m|| simpl (tc x) || = 1
m|| simpl (tvar n) || = 1
m|| simpl (mvar n) || = 1
m|| simpl (a →' b) || = suc (m|| a || N+ m|| b ||)
m|| a ⇒ b || = 1 N+ (m|| a || N+ m|| b ||)
m|| ∀' a || = 1 N+ m|| a ||

-- We package Type with it's deBruijn counter because
-- we need to express orderings such as a sρ< ∀' a
-- where the number of free variables varies.
-- We could express that as ∀ {ν μ} → Type ν → Type μ → Set,
-- but Well-founded _sρ<_ unifies ν and μ,
-- such that the well-founded proof would be too narrow
_sρ<_ : ∃ Type → ∃ Type → Set
(_ , a) sρ< (_ , b) = || a || N< || b ||

_m<_ : ∃₂ MetaType → ∃₂ MetaType → Set
(_ , _ , a) m< (_ , _ , b) = m|| a || N< m|| b ||

-- we can show that our strict size measure a ρ< b is well founded
-- by relating it to the well-foundedness proof of _<'_
sρ<-well-founded : Well-founded _sρ<_
sρ<-well-founded = sub.well-founded (image.well-founded <-well-founded)
  where
    module sub = Inverse-image (λ{ (_ , a) → || a ||})
    module image = Subrelation {A = ℕ} {_N<_} {_<′_} ≤⇒≤′

m<-well-founded : Well-founded _m<_
m<-well-founded = sub.well-founded (image.well-founded <-well-founded)
  where
    module sub = Inverse-image (λ{ (_ , _ , a) → m|| a ||})
    module image = Subrelation {A = ℕ} {_N<_} {_<′_} ≤⇒≤′

-- we also show that the ordering on stacks is well founded
s<-well-founded : ∀ {ν} {Δ : ICtx ν} → Well-founded (_s<_ {ν} {Δ})
s<-well-founded = sub.well-founded (image.well-founded <-well-founded)
  where
    open import Data.Nat.Base
    open import Data.Nat.Properties
    module sub = Inverse-image (λ{ s → ssum s})
    module image = Subrelation {A = ℕ} {_N<_} {_<′_} ≤⇒≤′

module TypeSubstSizeLemmas where
  open MetaTypeTypeSubst

  mutual
    ||a/Var|| : ∀ {m ν μ} (a : MetaType m ν) (s : Sub Fin ν μ) →
                m|| a /Var s || ≡ m|| a ||
    ||a/Var|| (a ⇒ b) s = cong₂ (λ u v → 1 N+ u N+ v) (||a/Var|| a s) (||a/Var|| b s)
    ||a/Var|| (∀' a) s = cong (λ u → 1 N+ u) (||a/Var|| a (s VarSubst.↑))
    ||a/Var|| (simpl (tvar x)) s = refl
    ||a/Var|| (simpl (mvar x)) s = refl
    ||a/Var|| (simpl (a →' b)) s = cong₂ (λ u v → 1 N+ u N+ v) (||a/Var|| a s) (||a/Var|| b s)
    ||a/Var|| (simpl (tc c)) s = refl

    ||weaken-a|| : ∀ {m ν} (a : MetaType m ν) → m|| weaken a || ≡ m|| a ||
    ||weaken-a|| {m} {ν} a = begin
      m|| weaken a ||
        ≡⟨ refl ⟩
      m|| a /Var VarSubst.wk ||
        ≡⟨ ||a/Var|| a VarSubst.wk ⟩
      m|| a || ∎

    ||s↑|| : ∀ {m ν μ} (s : Sub (MetaType m) ν μ) →
                       (∀ (x : Fin ν) → m|| lookup x s || ≡ 1) →
                       ∀ y → m|| lookup y (s ↑) || ≡ 1
    ||s↑|| s p zero = refl
    ||s↑|| s p (suc y) = begin
      m|| lookup y (map weaken s) ||
        ≡⟨ cong m||_|| (sym $ lookup⋆map s weaken y) ⟩
      m|| weaken (lookup y s) ||
        ≡⟨ ||weaken-a|| (lookup y s) ⟩
      m|| (lookup y s) ||
        ≡⟨ p y ⟩
      1 ∎
  
    ||a/s|| : ∀ {m ν μ} (a : MetaType m ν) (s : Sub (MetaType m) ν μ) →
             (∀ x → m|| lookup x s || ≡ 1) →
             m|| a / s || ≡ m|| a ||
    ||a/s|| (a ⇒ b) s p = cong₂ (λ u v → 1 N+ u N+ v) (||a/s|| a s p) (||a/s|| b s p)
    ||a/s|| (∀' a) s p = cong (λ u → 1 N+ u) (||a/s|| a (s ↑) (||s↑|| s p))
    ||a/s|| {m} {ν} (simpl (tvar x)) s p = begin
      m|| (simpl (tvar x)) / s ||
        ≡⟨ cong m||_|| (MetaTypeTypeLemmas.var-/ {x = x}) ⟩
      m|| lookup x s ||
        ≡⟨ p x ⟩
      1 ∎
    ||a/s|| (simpl (mvar x)) s p = refl
    ||a/s|| (simpl (a →' b)) s p = cong₂ (λ u v → 1 N+ u N+ v) (||a/s|| a s p) (||a/s|| b s p)
    ||a/s|| (simpl (tc c)) s p = refl
  
module MetaSubstSizeLemmas where
  open MetaTypeMetaSubst

  mutual
    ||a/Var|| : ∀ {ν m n} (a : MetaType m ν) (s : Sub Fin m n) →
                m|| a /Var s || ≡ m|| a ||
    ||a/Var|| (a ⇒ b) s = cong₂ (λ u v → 1 N+ u N+ v) (||a/Var|| a s) (||a/Var|| b s)
    ||a/Var|| (∀' a) s = cong (λ u → 1 N+ u) (||a/Var|| a s)
    ||a/Var|| (simpl (tvar x)) s = refl
    ||a/Var|| (simpl (mvar x)) s = refl
    ||a/Var|| (simpl (a →' b)) s = cong₂ (λ u v → 1 N+ u N+ v) (||a/Var|| a s) (||a/Var|| b s)
    ||a/Var|| (simpl (tc c)) s = refl

    ||weaken-a|| : ∀ {m ν} (a : MetaType m ν) → m|| weaken a || ≡ m|| a ||
    ||weaken-a|| {m} {ν} a = begin
      m|| weaken a ||
        ≡⟨ refl ⟩
      m|| a /Var VarSubst.wk ||
        ≡⟨ ||a/Var|| a VarSubst.wk ⟩
      m|| a || ∎

    ||s↑|| : ∀ {m ν μ} (s : Sub (MetaType m) ν μ) →
                       (∀ (x : Fin ν) → m|| lookup x s || ≡ 1) →
                       ∀ y → m|| lookup y (s ↑) || ≡ 1
    ||s↑|| s p zero = refl
    ||s↑|| s p (suc y) = begin
      m|| lookup y (map weaken s) ||
        ≡⟨ cong m||_|| (sym $ lookup⋆map s weaken y) ⟩
      m|| weaken (lookup y s) ||
        ≡⟨ ||weaken-a|| (lookup y s) ⟩
      m|| (lookup y s) ||
        ≡⟨ p y ⟩
      1 ∎
  
    ||a/s|| : ∀ {m ν n} (a : MetaType m ν) (s : Sub (flip MetaType ν) m n) →
             (∀ x → m|| lookup x s || ≡ 1) →
             m|| a / s || ≡ m|| a ||
    ||a/s|| (a ⇒ b) s p = cong₂ (λ u v → 1 N+ u N+ v) (||a/s|| a s p) (||a/s|| b s p)
    ||a/s|| (∀' a) s p = cong (λ u → 1 N+ u) (||a/s|| a (map MetaTypeTypeSubst.weaken s) lem)
      where
        lem : ∀ x → m|| lookup x (map MetaTypeTypeSubst.weaken s) || ≡ 1
        lem x = begin
          m|| lookup x (map MetaTypeTypeSubst.weaken s) ||
            ≡⟨ cong m||_|| (sym $ lookup⋆map s _ x) ⟩
          m|| MetaTypeTypeSubst.weaken (lookup x s) ||
            ≡⟨ TypeSubstSizeLemmas.||weaken-a|| (lookup x s) ⟩
          m|| lookup x s ||
            ≡⟨ p x ⟩
          1 ∎
    ||a/s|| {m} {ν} (simpl (mvar x)) s p = begin
      m|| (simpl (mvar x)) / s ||
        ≡⟨ cong m||_|| (MetaTypeTypeLemmas.var-/ {x = x}) ⟩
      m|| lookup x s ||
        ≡⟨ p x ⟩
      1 ∎
    ||a/s|| (simpl (tvar x)) s p = refl
    ||a/s|| (simpl (a →' b)) s p = cong₂ (λ u v → 1 N+ u N+ v) (||a/s|| a s p) (||a/s|| b s p)
    ||a/s|| (simpl (tc c)) s p = refl

||open-meta-a||≡a : ∀ {m ν} (a : MetaType m (suc ν)) → m|| open-meta a || ≡ m|| a ||
||open-meta-a||≡a {m} {ν} a = begin
  m|| open-meta a ||
    ≡⟨ TypeSubstSizeLemmas.||a/s|| (MMS.weaken a) (MTS.sub (simpl (mvar zero))) lem ⟩
  m|| (MMS.weaken a) ||
    ≡⟨ MetaSubstSizeLemmas.||weaken-a|| a ⟩
  m|| a || ∎
    where
      module MMS = MetaTypeMetaSubst
      module MTS = MetaTypeTypeSubst
      lem : ∀ (x : Fin (suc ν)) → m|| lookup x (MetaTypeTypeSubst.sub (simpl (mvar zero))) || ≡ 1
      lem zero = refl
      lem (suc x) =
        cong m||_|| (MetaTypeTypeLemmas.lookup-sub-↑⋆ {t = (simpl (mvar zero))} zero x)

a-sρ<-∀a : ∀ {n a} → (suc n , a) sρ< (, ∀' a)
a-sρ<-∀a = ≤-refl

b-sρ<-a⇒b : ∀ {ν} (a b : Type ν) → (_ , b) sρ< (_ , a ⇒ b)
b-sρ<-a⇒b a b = s≤s (≤-steps || a || ≤-refl)

a-m<-∀a : ∀ {m ν} a → (m , suc ν , a) m< (m , ν , ∀' a)
a-m<-∀a a = ≤-refl 

b-m<-a⇒b : ∀ {m ν} a b → (m , ν , b) m< (m , ν , a ⇒ b)
b-m<-a⇒b a b = s≤s (≤-steps m|| a || ≤-refl)

open-meta-a-m<-∀'a : ∀ {m ν} a → (suc m , ν , open-meta a) m< (m , ν , ∀' a)
open-meta-a-m<-∀'a a = subst (λ x → x N< m||  ∀' a ||) (sym $ ||open-meta-a||≡a a) (a-m<-∀a a)
