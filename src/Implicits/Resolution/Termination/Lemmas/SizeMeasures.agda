open import Prelude

module Implicits.Resolution.Termination.Lemmas.SizeMeasures
  where

open import Induction.WellFounded
open import Induction.Nat
open import Data.Fin.Substitution
open import Implicits.Syntax
open import Implicits.Syntax.Type.Unification
open import Implicits.Substitutions
open import Implicits.Substitutions.Lemmas
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
open import Relation.Binary using (module DecTotalOrder)
open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl)
open import Extensions.Nat
open import Implicits.Resolution.Termination.SizeMeasures

-- we can show that our size measure a ρ< b is well founded
-- by relating it to the well-foundedness proof of _<'_
open import Induction.WellFounded
ρ<-well-founded : Well-founded _ρ<_
ρ<-well-founded = sub.well-founded (image.well-founded <-well-founded)
    where
        open import Induction.Nat
        open import Data.Nat
        open import Data.Nat.Properties
        module sub = Inverse-image (λ{ (_ , a ) → || a ||})
        module image = Subrelation {A = ℕ} {_N<_} {_<′_} ≤⇒≤′

open import Induction.WellFounded
hρ<-well-founded : Well-founded _hρ<_
hρ<-well-founded = sub.well-founded (image.well-founded <-well-founded)
  where
    open import Induction.Nat
    open import Data.Nat
    open import Data.Nat.Properties
    module sub = Inverse-image (λ{ (_ , a ) → h|| a ||})
    module image = Subrelation {A = ℕ} {_N<_} {_<′_} ≤⇒≤′

m<-well-founded : Well-founded _m<_
m<-well-founded = sub.well-founded (image.well-founded <-well-founded)
    where
        module sub = Inverse-image (λ{ (_ , _ , a) → m|| a ||})
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
  open MetaTypeMetaSubst hiding (open-meta)

  mutual
    ||a/Var|| : ∀ {ν m n} (a : MetaType m ν) (s : Sub Fin m n) →
                m|| a /Var s || ≡ m|| a ||
    ||a/Var|| (a ⇒ b) s = cong₂ (λ u v → 1 N+ u N+ v) (||a/Var|| a s) (||a/Var|| b s)
    ||a/Var|| {ν = ν} (∀' a) s =
      cong (λ u → 1 N+ u) (||a/Var|| a ((varLift MetaLift.↑tp) {ν = ν} s))
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
        ≡⟨ ||weaken-a|| a ⟩
      m|| a || ∎
        where
          module MMS = MetaTypeMetaSubst
          module MTS = MetaTypeTypeSubst
          lem : ∀ (x : Fin (suc ν)) → m|| lookup x (MetaTypeTypeSubst.sub (simpl (mvar zero))) || ≡ 1
          lem zero = refl
          lem (suc x) =
            cong m||_|| (MetaTypeTypeLemmas.lookup-sub-↑⋆ {t = (simpl (mvar zero))} zero x)

module SubstSizeLemmas where
  open TypeLemmas

  mutual
    ||a|| : ∀ {ν} (a : Type ν) → || a || ≥ 1
    ||a|| (simpl (tc x)) = s≤s z≤n
    ||a|| (simpl (tvar n)) = s≤s z≤n
    ||a|| (simpl (a →' b)) = s≤s z≤n
    ||a|| (a ⇒ b) = s≤s z≤n
    ||a|| (∀' a) = s≤s z≤n

    ||a/Var|| : ∀ {ν μ} (a : Type ν) (s : Sub Fin ν μ) → || a /Var s || ≡ || a ||
    ||a/Var|| (a ⇒ b) s = cong₂ (λ u v → 1 N+ u N+ v) (||a/Var|| a s) (||a/Var|| b s)
    ||a/Var|| (∀' a) s = cong (λ u → 1 N+ u) (||a/Var|| a (s VarSubst.↑))
    ||a/Var|| (simpl (tvar x)) s = refl
    ||a/Var|| (simpl (a →' b)) s = cong₂ (λ u v → 1 N+ u N+ v) (||a/Var|| a s) (||a/Var|| b s)
    ||a/Var|| (simpl (tc c)) s = refl

    ||weaken-a|| : ∀ {ν} (a : Type ν) → || weaken a || ≡ || a ||
    ||weaken-a|| {ν} a = begin
      || weaken a ||
        ≡⟨ refl ⟩
      || a /Var VarSubst.wk ||
        ≡⟨ ||a/Var|| a VarSubst.wk ⟩
      || a || ∎

    ||s↑|| : ∀ {ν μ} (s : Sub Type ν μ) →
                       (∀ (x : Fin ν) → || lookup x s || ≡ 1) →
                       ∀ y → || lookup y (s ↑) || ≡ 1
    ||s↑|| s p zero = refl
    ||s↑|| s p (suc y) = begin
      || lookup y (map weaken s) ||
        ≡⟨ cong ||_|| (sym $ lookup⋆map s weaken y) ⟩
      || weaken (lookup y s) ||
        ≡⟨ ||weaken-a|| (lookup y s) ⟩
      || (lookup y s) ||
        ≡⟨ p y ⟩
      1 ∎
  
    ||a/s|| : ∀ {ν μ} (a : Type ν) (s : Sub Type ν μ) →
             (∀ x → || lookup x s || ≡ 1) →
             || a / s || ≡ || a ||
    ||a/s|| (a ⇒ b) s p = cong₂ (λ u v → 1 N+ u N+ v) (||a/s|| a s p) (||a/s|| b s p)
    ||a/s|| (∀' a) s p = cong (λ u → 1 N+ u) (||a/s|| a (s ↑) (||s↑|| s p))
    ||a/s|| {m} {ν} (simpl (tvar x)) s p = begin
      || (simpl (tvar x)) / s ||
        ≡⟨ cong ||_|| (var-/ {x = x}) ⟩
      || lookup x s ||
        ≡⟨ p x ⟩
      1 ∎
    ||a/s|| (simpl (a →' b)) s p = cong₂ (λ u v → 1 N+ u N+ v) (||a/s|| a s p) (||a/s|| b s p)
    ||a/s|| (simpl (tc c)) s p = refl

    ||a/wk↑k|| : ∀ {ν} k (a : Type (k N+ ν)) → || a / wk ↑⋆ k || ≡ || a ||
    ||a/wk↑k|| k a = ||a/s|| a (wk ↑⋆ k) (λ x → cong ||_|| (lookup-wk-↑⋆ k x))

    ||a/s||' : ∀ {ν μ} (a : Type ν) (s : Sub Type ν μ) → || a || N≤ || a / s ||
    ||a/s||' (simpl (tc x)) s = s≤s z≤n
    ||a/s||' (simpl (tvar n)) s = ||a|| (lookup n s)
    ||a/s||' (simpl (a →' b)) s = s≤s (<-+ (||a/s||' a s) (||a/s||' b s))
    ||a/s||' (a ⇒ b) s = s≤s (<-+ (||a/s||' a s) (||a/s||' b s))
    ||a/s||' (∀' b) s = s≤s (||a/s||' b (s TypeSubst.↑))

    h||a/s|| : ∀ {ν μ} (a : Type ν) (s : Sub Type ν μ) → (, a) hρ≤ (, a / s)
    h||a/s|| (simpl (tc x)) s = s≤s z≤n
    h||a/s|| (simpl (tvar n)) s = ||a|| (proj₂ (lookup n s ◁))
    h||a/s|| (simpl (a →' b)) s = s≤s (<-+ (||a/s||' a s) (||a/s||' b s))
    h||a/s|| (a ⇒ b) s = h||a/s|| b s
    h||a/s|| (∀' b) s = h||a/s|| b (s TypeSubst.↑)

a-ρ<-∀a : ∀ {n} a → (suc n , a) ρ< (, ∀' a)
a-ρ<-∀a _ = ≤-refl

b-ρ<-a⇒b : ∀ {ν} (a b : Type ν) → (_ , b) ρ< (_ , a ⇒ b)
b-ρ<-a⇒b a b = s≤s (≤-steps || a || ≤-refl)

b-hρ≤-a⇒b : ∀ {ν} (a b : Type ν) → (_ , b) hρ≤ (_ , a ⇒ b)
b-hρ≤-a⇒b a b = subst (λ u → u N≤ h|| a ⇒ b ||) refl ≤-refl

a-m<-∀a : ∀ {m ν} a → (m , suc ν , a) m< (m , ν , ∀' a)
a-m<-∀a a = ≤-refl 

b-m<-a⇒b : ∀ {m ν} a b → (m , ν , b) m< (m , ν , a ⇒ b)
b-m<-a⇒b a b = s≤s (≤-steps m|| a || ≤-refl)

open-meta-a-m<-∀'a : ∀ {m ν} a → (suc m , ν , open-meta a) m< (m , ν , ∀' a)
open-meta-a-m<-∀'a a = subst (λ x → x N< m||  ∀' a ||)
  (sym $ MetaSubstSizeLemmas.||open-meta-a||≡a a) (a-m<-∀a a)
