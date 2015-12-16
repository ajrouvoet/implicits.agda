open import Prelude

module Implicits.Semantics.Lemmas
  (TC : Set)
  (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import SystemF TC as F using ()
open import Extensions.ListFirst
open import Data.Fin.Substitution
open import Data.Vec.Properties

open import Implicits.Syntax TC _tc≟_
open import Implicits.WellTyped TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open import Implicits.Substitutions.Lemmas TC _tc≟_
open import Implicits.Semantics.Type TC _tc≟_
open import Implicits.Semantics.Context TC _tc≟_

private
  module TS = TypeSubst

⟦a/var⟧ : ∀ {ν ν'} (a : Type ν) (s : Sub Fin ν ν') → ⟦ a TS./Var s ⟧tp→ ≡ ⟦ a ⟧tp→ F./Var s
⟦a/var⟧ (simpl (tc x)) s = refl
⟦a/var⟧ (simpl (tvar n)) s = refl
⟦a/var⟧ (simpl (a →' b)) s = cong₂ F._→'_ (⟦a/var⟧ a s) (⟦a/var⟧ b s)
⟦a/var⟧ (a ⇒ b) s = cong₂ F._→'_ (⟦a/var⟧ a s) (⟦a/var⟧ b s)
⟦a/var⟧ (∀' a) s = cong F.∀' (⟦a/var⟧ a (s VarSubst.↑))

⟦weaken⟧ : ∀ {ν} (a : Type ν) → ⟦ TS.weaken a ⟧tp→ ≡ F.weaken ⟦ a ⟧tp→
⟦weaken⟧ x = ⟦a/var⟧ x VarSubst.wk

-- helper lemma on mapping type-semantics over weakend substitutions
⟦weaken⟧tps→ : ∀ {ν n} (xs : Vec (Type ν) n) →
               ⟦ (map TS.weaken xs) ⟧tps→ ≡ (map F.weaken ⟦ xs ⟧tps→)
⟦weaken⟧tps→ xs = begin
  (map ⟦_⟧tp→ ∘ map TS.weaken) xs
    ≡⟨ sym $ (map-∘ ⟦_⟧tp→ TS.weaken) xs ⟩
  map (⟦_⟧tp→ ∘ TS.weaken) xs
    ≡⟨ (map-cong ⟦weaken⟧) xs ⟩
  map (F.weaken ∘ ⟦_⟧tp→) xs
    ≡⟨ (map-∘ F.weaken ⟦_⟧tp→) xs ⟩ 
  map F.weaken (map ⟦_⟧tp→ xs) ∎

-- the semantics of identity type-substitution is exactly 
-- system-f's identity type substitution
⟦id⟧tp→ : ∀ {n} → map ⟦_⟧tp→ (TS.id {n}) ≡ F.id
⟦id⟧tp→ {zero} = refl
⟦id⟧tp→ {suc n} = begin
  map ⟦_⟧tp→ (simpl (tvar zero) ∷ map TS.weaken (TS.id {n})) 
    ≡⟨ refl ⟩
  F.tvar zero ∷ (map ⟦_⟧tp→ (map TS.weaken (TS.id {n}))) 
    ≡⟨ cong (_∷_ (F.tvar zero)) (⟦weaken⟧tps→ (TS.id {n})) ⟩
  F.tvar zero ∷ (map F.weaken (map ⟦_⟧tp→ (TS.id {n}))) 
    ≡⟨ cong (λ e → F.tvar zero ∷ (map F.weaken e)) ⟦id⟧tp→ ⟩
  F.tvar zero ∷ (map F.weaken (F.id {n})) 
    ≡⟨ refl ⟩
  F.id ∎

-- the semantics of type weakening is exactly system-f's type weakening
⟦wk⟧tp→ : ∀ {n} → map ⟦_⟧tp→ (TS.wk {n}) ≡ F.wk {n}
⟦wk⟧tp→ = begin
  map ⟦_⟧tp→ TS.wk 
    ≡⟨ ⟦weaken⟧tps→ TS.id ⟩
  map F.weaken (map ⟦_⟧tp→ TS.id) 
    ≡⟨ cong (map F.weaken) ⟦id⟧tp→ ⟩
  F.wk ∎

⟦↑⟧tps→ :  ∀ {ν n} (v : Vec (Type ν) n) → ⟦ v TS.↑ ⟧tps→ ≡ ⟦ v ⟧tps→ F.↑
⟦↑⟧tps→ xs = begin
  F.tvar zero ∷ (map ⟦_⟧tp→ (map TS.weaken xs)) 
    ≡⟨ cong (_∷_ (F.tvar zero)) (⟦weaken⟧tps→ xs) ⟩
  F.tvar zero ∷ (map F.weaken (map ⟦_⟧tp→ xs)) 
    ≡⟨ refl ⟩
  (map ⟦_⟧tp→ xs) F.↑ ∎

-- lookup in and interpreted context Γ is equivalent to interpreting a type, looked up in K
lookup-⟦⟧ctx→ : ∀ {ν n} (K : Ktx ν n) x → ⟦ lookup x $ proj₁ K ⟧tp→ ≡ lookup x ⟦ K ⟧ctx→
lookup-⟦⟧ctx→ K x = lookup⋆map (proj₁ K) ⟦_⟧tp→ x

-- type substitution commutes with interpreting types
⟦a/s⟧tp→ : ∀ {ν μ} (tp : Type ν) (σ : Sub Type ν μ) → ⟦ tp TS./ σ ⟧tp→ ≡ ⟦ tp ⟧tp→ F./ (map ⟦_⟧tp→ σ)
⟦a/s⟧tp→ (simpl (tc c)) σ = refl
⟦a/s⟧tp→  (simpl (tvar n)) σ = begin
  ⟦ lookup n σ ⟧tp→ 
    ≡⟨ lookup⋆map σ ⟦_⟧tp→ n ⟩
  ⟦ simpl (tvar n) ⟧tp→ F./ (map ⟦_⟧tp→ σ) ∎
⟦a/s⟧tp→ (l ⇒ r) σ = cong₂ F._→'_ (⟦a/s⟧tp→ l σ) (⟦a/s⟧tp→ r σ)
⟦a/s⟧tp→ (simpl (l →' r)) σ = cong₂ F._→'_ (⟦a/s⟧tp→ l σ) (⟦a/s⟧tp→ r σ)
⟦a/s⟧tp→ (∀' a) σ = begin
  F.∀' ⟦ (a TS./ σ TS.↑) ⟧tp→
    ≡⟨ cong F.∀' (⟦a/s⟧tp→ a (σ TS.↑)) ⟩
  F.∀' (⟦ a ⟧tp→ F./ ⟦ σ TS.↑ ⟧tps→)
    ≡⟨ cong (λ u → F.∀' (⟦ a ⟧tp→ F./ u)) ((⟦↑⟧tps→ σ)) ⟩
  ⟦ ∀' a ⟧tp→ F./ (map ⟦_⟧tp→ σ) ∎

-- forall' application commutes with interpreting types
⟦a/sub⟧tp→ : ∀ {ν} (a : Type (suc ν)) b → ⟦ a TS./ (TS.sub b) ⟧tp→ ≡ ⟦ a ⟧tp→ F./ (F.sub ⟦ b ⟧tp→)
⟦a/sub⟧tp→ a b = begin
  ⟦ a TS./ (TS.sub b) ⟧tp→
  ≡⟨ ⟦a/s⟧tp→ a (b ∷ TS.id) ⟩
  (⟦ a ⟧tp→ F./ (map ⟦_⟧tp→ (b ∷ TS.id)) )
  ≡⟨ refl ⟩
  (⟦ a ⟧tp→ F./ (⟦ b ⟧tp→ ∷ (map ⟦_⟧tp→ TS.id)) )
  ≡⟨ cong (λ s → ⟦ a ⟧tp→ F./ (⟦ b ⟧tp→ ∷ s)) ⟦id⟧tp→ ⟩
  (⟦ a ⟧tp→ F./ (F.sub ⟦ b ⟧tp→)) ∎

⟦a/wk⟧tp→ : ∀ {ν} (tp : Type ν) → ⟦ tp TS./ TS.wk ⟧tp→ ≡ ⟦ tp ⟧tp→ F./ F.wk
⟦a/wk⟧tp→ tp = begin
  ⟦ tp TS./ TS.wk ⟧tp→
    ≡⟨ ⟦a/s⟧tp→ tp TS.wk ⟩
  ⟦ tp ⟧tp→ F./ (map ⟦_⟧tp→ TS.wk) 
    ≡⟨ cong (λ e → ⟦ tp ⟧tp→ F./ e) ⟦wk⟧tp→ ⟩
  ⟦ tp ⟧tp→ F./ F.wk ∎

-- type weakening commutes with interpreting types
⟦weaken⟧tp→ : ∀ {ν} (tp : Type ν) → ⟦ tp-weaken tp ⟧tp→ ≡ F.tp-weaken ⟦ tp ⟧tp→
⟦weaken⟧tp→ tp = begin
  ⟦ tp-weaken tp ⟧tp→
    ≡⟨ cong ⟦_⟧tp→ (sym $ TypeLemmas./-wk {t = tp})⟩
  ⟦ tp TS./ TS.wk ⟧tp→
    ≡⟨ ⟦a/wk⟧tp→ tp ⟩
  ⟦ tp ⟧tp→ F./ F.wk
    ≡⟨ F./-wk {t = ⟦ tp ⟧tp→} ⟩
  F.tp-weaken ⟦ tp ⟧tp→ ∎

-- context weakening commutes with interpreting contexts
⟦weaken⟧ctx→ : ∀ {ν n} (K : Ktx ν n) → ⟦ ktx-weaken K ⟧ctx→ ≡ F.ctx-weaken ⟦ K ⟧ctx→
⟦weaken⟧ctx→ ([] , Δ) = refl
⟦weaken⟧ctx→ (x ∷ Γ , Δ) with ⟦weaken⟧ctx→ (Γ , Δ)
⟦weaken⟧ctx→ (x ∷ Γ , Δ) | ih = begin
  ⟦ ktx-weaken (x ∷ Γ , Δ) ⟧ctx→ ≡⟨ refl ⟩ 
  ⟦ x TS./ TS.wk ⟧tp→ ∷ xs ≡⟨ cong (flip _∷_ xs) (⟦a/wk⟧tp→ x) ⟩
  (⟦ x ⟧tp→ F./ F.wk) ∷ ⟦ ktx-weaken (Γ , Δ) ⟧ctx→ ≡⟨ cong (_∷_ (⟦ x ⟧tp→ F./ F.wk)) ih ⟩
  (⟦ x ⟧tp→ F./ F.wk) ∷ F.ctx-weaken ⟦ Γ , Δ ⟧ctx→ ≡⟨ refl ⟩
  F.ctx-weaken ⟦ x ∷ Γ , Δ ⟧ctx→ ∎
  where
    xs = map ⟦_⟧tp→ $ map (λ s → s TS./ TS.wk ) Γ
  
