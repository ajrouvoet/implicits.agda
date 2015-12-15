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
⟦⟧tps→⋆weaken : ∀ {ν n} (xs : Vec (Type ν) n) →
               ⟦ (map TS.weaken xs) ⟧tps→ ≡ (map F.weaken ⟦ xs ⟧tps→)
⟦⟧tps→⋆weaken xs = begin
  (map ⟦_⟧tp→ ∘ map TS.weaken) xs
    ≡⟨ sym $ (map-∘ ⟦_⟧tp→ TS.weaken) xs ⟩
  map (⟦_⟧tp→ ∘ TS.weaken) xs
    ≡⟨ (map-cong ⟦weaken⟧) xs ⟩
  map (F.weaken ∘ ⟦_⟧tp→) xs
    ≡⟨ (map-∘ F.weaken ⟦_⟧tp→) xs ⟩ 
  map F.weaken (map ⟦_⟧tp→ xs) ∎

-- the semantics of identity type-substitution is exactly 
-- system-f's identity type substitution
⟦id⟧≡fid : ∀ {n} → map ⟦_⟧tp→ (TS.id {n}) ≡ F.id
⟦id⟧≡fid {zero} = refl
⟦id⟧≡fid {suc n} = begin
  map ⟦_⟧tp→ (simpl (tvar zero) ∷ map TS.weaken (TS.id {n})) 
    ≡⟨ refl ⟩
  F.tvar zero ∷ (map ⟦_⟧tp→ (map TS.weaken (TS.id {n}))) 
    ≡⟨ cong (_∷_ (F.tvar zero)) (⟦⟧tps→⋆weaken (TS.id {n})) ⟩
  F.tvar zero ∷ (map F.weaken (map ⟦_⟧tp→ (TS.id {n}))) 
    ≡⟨ cong (λ e → F.tvar zero ∷ (map F.weaken e)) ⟦id⟧≡fid ⟩
  F.tvar zero ∷ (map F.weaken (F.id {n})) 
    ≡⟨ refl ⟩
  F.id ∎

-- the semantics of type weakening is exactly system-f's type weakening
⟦wk⟧≡fwk : ∀ {n} → map ⟦_⟧tp→ (TS.wk {n}) ≡ F.wk {n}
⟦wk⟧≡fwk = begin
  map ⟦_⟧tp→ TS.wk 
    ≡⟨ ⟦⟧tps→⋆weaken TS.id ⟩
  map F.weaken (map ⟦_⟧tp→ TS.id) 
    ≡⟨ cong (map F.weaken) ⟦id⟧≡fid ⟩
  F.wk ∎

⟦⟧tps→⋆↑ :  ∀ {ν n} (v : Vec (Type ν) n) → ⟦ v TS.↑ ⟧tps→ ≡ ⟦ v ⟧tps→ F.↑
⟦⟧tps→⋆↑ xs = begin
  F.tvar zero ∷ (map ⟦_⟧tp→ (map TS.weaken xs)) 
    ≡⟨ cong (_∷_ (F.tvar zero)) (⟦⟧tps→⋆weaken xs) ⟩
  F.tvar zero ∷ (map F.weaken (map ⟦_⟧tp→ xs)) 
    ≡⟨ refl ⟩
  (map ⟦_⟧tp→ xs) F.↑ ∎

-- lookup in and interpreted context Γ is equivalent to interpreting a type, looked up in K
lookup⋆⟦⟧ctx : ∀ {ν n} (K : Ktx ν n) x → lookup x ⟦ K ⟧ctx ≡ ⟦ lookup x $ proj₁ K ⟧tp→
lookup⋆⟦⟧ctx K x = sym $ lookup⋆map (proj₁ K) ⟦_⟧tp→ x

-- type substitution commutes with interpreting types
/⋆⟦⟧tp→ : ∀ {ν μ} (tp : Type ν) (σ : Sub Type ν μ) → ⟦ tp TS./ σ ⟧tp→ ≡ ⟦ tp ⟧tp→ F./ (map ⟦_⟧tp→ σ)
/⋆⟦⟧tp→ (simpl (tc c)) σ = refl
/⋆⟦⟧tp→ (simpl (tvar n)) σ = begin
  ⟦ lookup n σ ⟧tp→ 
    ≡⟨ lookup⋆map σ ⟦_⟧tp→ n ⟩
  ⟦ simpl (tvar n) ⟧tp→ F./ (map ⟦_⟧tp→ σ) ∎
/⋆⟦⟧tp→ (l ⇒ r) σ = cong₂ F._→'_ (/⋆⟦⟧tp→ l σ) (/⋆⟦⟧tp→ r σ)
/⋆⟦⟧tp→ (simpl (l →' r)) σ = cong₂ F._→'_ (/⋆⟦⟧tp→ l σ) (/⋆⟦⟧tp→ r σ)
/⋆⟦⟧tp→ (∀' a) σ = begin
  F.∀' ⟦ (a TS./ σ TS.↑) ⟧tp→
    ≡⟨ cong F.∀' (/⋆⟦⟧tp→ a (σ TS.↑)) ⟩
  F.∀' (⟦ a ⟧tp→ F./ ⟦ σ TS.↑ ⟧tps→)
    ≡⟨ cong (λ u → F.∀' (⟦ a ⟧tp→ F./ u)) ((⟦⟧tps→⋆↑ σ)) ⟩
  ⟦ ∀' a ⟧tp→ F./ (map ⟦_⟧tp→ σ) ∎

-- forall' application commutes with interpreting types
⟦sub⟧≡sub⟦⟧ : ∀ {ν} (a : Type (suc ν)) b → ⟦ a TS./ (TS.sub b) ⟧tp→ ≡ ⟦ a ⟧tp→ F./ (F.sub ⟦ b ⟧tp→)
⟦sub⟧≡sub⟦⟧ a b = begin
  ⟦ a TS./ (TS.sub b) ⟧tp→
  ≡⟨ /⋆⟦⟧tp→ a (b ∷ TS.id) ⟩
  (⟦ a ⟧tp→ F./ (map ⟦_⟧tp→ (b ∷ TS.id)) )
  ≡⟨ refl ⟩
  (⟦ a ⟧tp→ F./ (⟦ b ⟧tp→ ∷ (map ⟦_⟧tp→ TS.id)) )
  ≡⟨ cong (λ s → ⟦ a ⟧tp→ F./ (⟦ b ⟧tp→ ∷ s)) ⟦id⟧≡fid ⟩
  (⟦ a ⟧tp→ F./ (F.sub ⟦ b ⟧tp→)) ∎

/-wk⋆⟦⟧tp→ : ∀ {ν} (tp : Type ν) → ⟦ tp TS./ TS.wk ⟧tp→ ≡ ⟦ tp ⟧tp→ F./ F.wk
/-wk⋆⟦⟧tp→ tp = begin
  ⟦ tp TS./ TS.wk ⟧tp→
    ≡⟨ /⋆⟦⟧tp→ tp TS.wk ⟩
  ⟦ tp ⟧tp→ F./ (map ⟦_⟧tp→ TS.wk) 
    ≡⟨ cong (λ e → ⟦ tp ⟧tp→ F./ e) ⟦wk⟧≡fwk ⟩
  ⟦ tp ⟧tp→ F./ F.wk ∎

-- type weakening commutes with interpreting types
weaken-tp⋆⟦⟧tp→ : ∀ {ν} (tp : Type ν) → ⟦ tp-weaken tp ⟧tp→ ≡ F.tp-weaken ⟦ tp ⟧tp→
weaken-tp⋆⟦⟧tp→ tp = begin
  ⟦ tp-weaken tp ⟧tp→
    ≡⟨ cong ⟦_⟧tp→ (sym $ TypeLemmas./-wk {t = tp})⟩
  ⟦ tp TS./ TS.wk ⟧tp→
    ≡⟨ /-wk⋆⟦⟧tp→ tp ⟩
  ⟦ tp ⟧tp→ F./ F.wk
    ≡⟨ F./-wk {t = ⟦ tp ⟧tp→} ⟩
  F.tp-weaken ⟦ tp ⟧tp→ ∎

-- context weakening commutes with interpreting contexts
ctx-weaken⋆⟦⟧ctx : ∀ {ν n} (K : Ktx ν n) → ⟦ ktx-weaken K ⟧ctx ≡ F.ctx-weaken ⟦ K ⟧ctx
ctx-weaken⋆⟦⟧ctx ([] , Δ) = refl
ctx-weaken⋆⟦⟧ctx (x ∷ Γ , Δ) with ctx-weaken⋆⟦⟧ctx (Γ , Δ)
ctx-weaken⋆⟦⟧ctx (x ∷ Γ , Δ) | ih = begin
  ⟦ ktx-weaken (x ∷ Γ , Δ) ⟧ctx ≡⟨ refl ⟩ 
  ⟦ x TS./ TS.wk ⟧tp→ ∷ xs ≡⟨ cong (flip _∷_ xs) (/-wk⋆⟦⟧tp→ x) ⟩
  (⟦ x ⟧tp→ F./ F.wk) ∷ ⟦ ktx-weaken (Γ , Δ) ⟧ctx ≡⟨ cong (_∷_ (⟦ x ⟧tp→ F./ F.wk)) ih ⟩
  (⟦ x ⟧tp→ F./ F.wk) ∷ F.ctx-weaken ⟦ Γ , Δ ⟧ctx ≡⟨ refl ⟩
  F.ctx-weaken ⟦ x ∷ Γ , Δ ⟧ctx ∎
  where
    xs = map ⟦_⟧tp→ $ map (λ s → s TS./ TS.wk ) Γ
  
