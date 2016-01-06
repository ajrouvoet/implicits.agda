open import Prelude
open import Function.Equivalence using (_⇔_; equivalence)
open import Data.Fin.Substitution
open import Data.List.Properties
open import Relation.Binary.HeterogeneousEquality as H using ()
module HR = H.≅-Reasoning
open import Data.Vec.Properties as VP using ()
open import Relation.Nullary.Decidable as Dec using ()

module Implicits.Resolution.Ambiguous.Undecidable TC _tc≟_ where

open import Implicits.Syntax TC _tc≟_
open import Implicits.Resolution.Ambiguous.Resolution TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open import Implicits.Substitutions.Lemmas TC _tc≟_
open import Implicits.Resolution.Ambiguous.Semantics TC _tc≟_
open TypeSubst hiding (subst)

private
  module TS = TypeSubst

open import SystemF TC as F using ()

module Embedding where
  ⟦_⟧tp← : ∀ {ν} → F.Type ν → Type ν
  ⟦ F.tc x ⟧tp← = simpl (tc x)
  ⟦ F.tvar n ⟧tp← = simpl (tvar n)
  ⟦ a F.→' b ⟧tp← = (⟦ a ⟧tp← ⇒ ⟦ b ⟧tp←)
  ⟦ a F.⟶ b ⟧tp← = simpl (⟦ a ⟧tp← →' ⟦ b ⟧tp←)
  ⟦ F.∀' x ⟧tp← = ∀' ⟦ x ⟧tp←

  ⟦_⟧tps← : ∀ {ν n} → Vec (F.Type ν) n → Vec (Type ν) n
  ⟦ v ⟧tps← = map (⟦_⟧tp←) v

  ⟦_⟧ctx← : ∀ {ν n} → Vec (F.Type ν) n → List (Type ν)
  ⟦ v ⟧ctx← = toList $ map ⟦_⟧tp← v

  ⟦_⟧tp→ : ∀ {ν} → Type ν → F.Type ν
  ⟦ simpl (tc x) ⟧tp→ = F.tc x
  ⟦ simpl (tvar n) ⟧tp→ = F.tvar n
  ⟦ simpl (a →' b) ⟧tp→ = ⟦ a ⟧tp→ F.⟶ ⟦ b ⟧tp→
  ⟦ a ⇒ b ⟧tp→ = ⟦ a ⟧tp→ F.→' ⟦ b ⟧tp→
  ⟦ ∀' x ⟧tp→ = F.∀' ⟦ x ⟧tp→

  ⟦_⟧tps→ : ∀ {ν n} → Vec (Type ν) n → Vec (F.Type ν) n
  ⟦ v ⟧tps→ = map (⟦_⟧tp→) v

  ⟦_⟧ctx→ : ∀ {ν} → (Δ : ICtx ν) → Vec (F.Type ν) (List.length (List.map ⟦_⟧tp→ Δ))
  ⟦ Δ ⟧ctx→ = fromList (List.map ⟦_⟧tp→ Δ)

module Lemmas where
  open Embedding

  length-weaken-Δ : ∀ {ν} (Δ : ICtx ν) →
    (List.length (List.map ⟦_⟧tp→ (ictx-weaken Δ))) ≡ (List.length (List.map ⟦_⟧tp→ Δ))
  length-weaken-Δ Δ = begin 
    (List.length (List.map ⟦_⟧tp→ (List.map (λ s → s / wk) Δ)))
      ≡⟨ cong List.length (sym $ map-compose Δ) ⟩
    (List.length (List.map (⟦_⟧tp→ ∘ (λ s → s / wk)) Δ))
      ≡⟨ length-map _ Δ ⟩
    List.length Δ
      ≡⟨ sym $ length-map _ Δ ⟩
    (List.length (List.map ⟦_⟧tp→ Δ)) ∎
  
  ⟦_⟧term→ : ∀ {ν} {Δ : ICtx ν} {r} → Δ ⊢ᵣ r → F.Term ν (List.length (List.map ⟦_⟧tp→ Δ))
  ⟦_⟧term→ {ν} {Δ} (r-tabs x) = F.Λ (subst (F.Term (suc ν)) (length-weaken-Δ Δ) ⟦ x ⟧term→)
  ⟦ r-tapp a x ⟧term→ = ⟦ x ⟧term→ F.[ ⟦ a ⟧tp→ ]
  ⟦_⟧term→ {Δ = Δ} (r-ivar x) =
    F.var (subst Fin (sym $ length-map _ Δ) (proj₁ $ ∈⟶index (VP.List-∈⇒∈ x)))
  ⟦ r-iabs {a = a} x ⟧term→ = F.λ' ⟦ a ⟧tp→ ⟦ x ⟧term→
  ⟦ r-iapp f e ⟧term→ = ⟦ f ⟧term→ F.· ⟦ e ⟧term→
  
  
  tp→← : ∀ {ν} (a : Type ν) → ⟦ ⟦ a ⟧tp→ ⟧tp← ≡ a
  tp→← (simpl (tc x)) = refl
  tp→← (simpl (tvar n)) = refl
  tp→← (simpl (x →' x₁)) = cong₂ (λ u v → simpl (u →' v)) (tp→← x) (tp→← x₁)
  tp→← (a ⇒ b) = cong₂ _⇒_ (tp→← a) (tp→← b)
  tp→← (∀' a) = cong ∀' (tp→← a)
  
  tp←→ : ∀ {ν} (a : F.Type ν) → ⟦ ⟦ a ⟧tp← ⟧tp→ ≡ a
  tp←→ (F.tc x) = refl
  tp←→ (F.tvar n) = refl
  tp←→ (x F.→' x₁) = cong₂ F._→'_ (tp←→ x) (tp←→ x₁)
  tp←→ (a F.⟶ b) = cong₂ F._⟶_ (tp←→ a) (tp←→ b)
  tp←→ (F.∀' a) = cong F.∀' (tp←→ a)
  
  ctx→← : ∀ {ν} (Δ : ICtx ν) → ⟦ ⟦ Δ ⟧ctx→ ⟧ctx← ≡ Δ
  ctx→← List.[] = refl
  ctx→← (x List.∷ xs) = begin
    ⟦ ⟦ x List.∷ xs ⟧ctx→ ⟧ctx←
      ≡⟨ refl ⟩
    toList (map ⟦_⟧tp← (fromList (List.map ⟦_⟧tp→ (x List.∷ xs))))
      ≡⟨ refl ⟩
    ⟦ ⟦ x ⟧tp→ ⟧tp← List.∷ (toList (map ⟦_⟧tp← (fromList (List.map ⟦_⟧tp→ xs))))
      ≡⟨ cong₂ List._∷_ (tp→← x) (ctx→← xs) ⟩
    (x List.∷ xs) ∎
  
  ⟦a/var⟧tp← : ∀ {ν ν'} (a : F.Type ν) (s : Vec (Fin ν') ν) → ⟦ a F./Var s ⟧tp← ≡ ⟦ a ⟧tp← /Var s
  ⟦a/var⟧tp← (F.tc x) s = refl
  ⟦a/var⟧tp← (F.tvar n) s = refl
  ⟦a/var⟧tp← (a F.→' b) s = cong₂ _⇒_ (⟦a/var⟧tp← a s) (⟦a/var⟧tp← b s)
  ⟦a/var⟧tp← (a F.⟶ b) s = cong₂ (λ u v → simpl (u →' v)) (⟦a/var⟧tp← a s) (⟦a/var⟧tp← b s)
  ⟦a/var⟧tp← (F.∀' a) s = cong ∀' (⟦a/var⟧tp← a (s VarSubst.↑))
  
  ⟦a/var⟧tp→ : ∀ {ν ν'} (a : Type ν) (s : Vec (Fin ν') ν) → ⟦ a /Var s ⟧tp→ ≡ ⟦ a ⟧tp→ F./Var s
  ⟦a/var⟧tp→ (simpl (tc x)) s = refl
  ⟦a/var⟧tp→ (simpl (tvar n)) s = refl
  ⟦a/var⟧tp→ (simpl (a →' b)) s = cong₂ F._⟶_ (⟦a/var⟧tp→ a s) (⟦a/var⟧tp→ b s)
  ⟦a/var⟧tp→ (a ⇒ b) s = cong₂ F._→'_ (⟦a/var⟧tp→ a s) (⟦a/var⟧tp→ b s)
  ⟦a/var⟧tp→ (∀' a) s = cong F.∀' (⟦a/var⟧tp→ a (s VarSubst.↑))
  
  ⟦weaken⟧tp← : ∀ {ν} (a : F.Type ν) → ⟦ F.weaken a ⟧tp← ≡ weaken ⟦ a ⟧tp←
  ⟦weaken⟧tp← x = ⟦a/var⟧tp← x VarSubst.wk
  
  ⟦weaken⟧tp→ : ∀ {ν} (a : Type ν) → ⟦ weaken a ⟧tp→ ≡ F.weaken ⟦ a ⟧tp→
  ⟦weaken⟧tp→ x = ⟦a/var⟧tp→ x VarSubst.wk
  
  -- helper lemma on mapping type-semantics over weakend substitutions
  ⟦⟧tps←⋆weaken : ∀ {ν n} (xs : Vec (F.Type ν) n) →
                 ⟦ (map F.weaken xs) ⟧tps← ≡ (map weaken ⟦ xs ⟧tps←)
  ⟦⟧tps←⋆weaken xs = begin
    (map ⟦_⟧tp← ∘ map F.weaken) xs
      ≡⟨ sym $ (VP.map-∘ ⟦_⟧tp← F.weaken) xs ⟩
    map (⟦_⟧tp← ∘ F.weaken) xs
    ≡⟨ (VP.map-cong ⟦weaken⟧tp←) xs ⟩
    map (TS.weaken ∘ ⟦_⟧tp←) xs
      ≡⟨ (VP.map-∘ TS.weaken ⟦_⟧tp←) xs ⟩ 
    map TS.weaken (map ⟦_⟧tp← xs) ∎
  
  -- helper lemma on mapping type-semantics over weakend substitutions
  ⟦⟧tps→⋆weaken : ∀ {ν n} (xs : Vec (Type ν) n) →
                 ⟦ (map TS.weaken xs) ⟧tps→ ≡ (map F.weaken ⟦ xs ⟧tps→)
  ⟦⟧tps→⋆weaken xs = begin
    (map ⟦_⟧tp→ ∘ map TS.weaken) xs
      ≡⟨ sym $ (VP.map-∘ ⟦_⟧tp→ TS.weaken) xs ⟩
    map (⟦_⟧tp→ ∘ TS.weaken) xs
    ≡⟨ (VP.map-cong ⟦weaken⟧tp→) xs ⟩
    map (F.weaken ∘ ⟦_⟧tp→) xs
      ≡⟨ (VP.map-∘ F.weaken ⟦_⟧tp→) xs ⟩ 
    map F.weaken (map ⟦_⟧tp→ xs) ∎
  
  -- the semantics of identity type-substitution is exactly 
  -- system-f's identity type substitution
  ⟦id⟧tp← : ∀ {n} → map ⟦_⟧tp← (F.id {n}) ≡ TS.id
  ⟦id⟧tp← {zero} = refl
  ⟦id⟧tp← {suc n} = begin
    map ⟦_⟧tp← (F.tvar zero ∷ map F.weaken (F.id {n})) 
      ≡⟨ refl ⟩
    (simpl (tvar zero)) ∷ (map ⟦_⟧tp← (map F.weaken (F.id {n}))) 
      ≡⟨ cong (_∷_ (simpl (tvar zero))) (⟦⟧tps←⋆weaken (F.id {n})) ⟩
    (simpl (tvar zero)) ∷ (map TS.weaken (map ⟦_⟧tp← (F.id {n}))) 
      ≡⟨ cong (λ e → simpl (tvar zero) ∷ (map TS.weaken e)) ⟦id⟧tp← ⟩
    (simpl (tvar zero)) ∷ (map TS.weaken (TS.id {n})) 
      ≡⟨ refl ⟩
    TS.id ∎
  
  -- the semantics of identity type-substitution is exactly 
  -- system-f's identity type substitution
  ⟦id⟧tp→ : ∀ {n} → map ⟦_⟧tp→ (TS.id {n}) ≡ F.id
  ⟦id⟧tp→ {zero} = refl
  ⟦id⟧tp→ {suc n} = begin
    map ⟦_⟧tp→ (simpl (tvar zero) ∷ map TS.weaken (TS.id {n})) 
      ≡⟨ refl ⟩
    F.tvar zero ∷ (map ⟦_⟧tp→ (map TS.weaken (TS.id {n}))) 
      ≡⟨ cong (_∷_ (F.tvar zero)) (⟦⟧tps→⋆weaken (TS.id {n})) ⟩
    F.tvar zero ∷ (map F.weaken (map ⟦_⟧tp→ (TS.id {n}))) 
      ≡⟨ cong (λ e → F.tvar zero ∷ (map F.weaken e)) ⟦id⟧tp→ ⟩
    F.tvar zero ∷ (map F.weaken (F.id {n})) 
      ≡⟨ refl ⟩
    F.id ∎
  
  -- the semantics of type weakening is exactly system-f's type weakening
  ⟦wk⟧tp← : ∀ {n} → map ⟦_⟧tp← (F.wk {n}) ≡ TS.wk {n}
  ⟦wk⟧tp← = begin
    map ⟦_⟧tp← F.wk 
      ≡⟨ ⟦⟧tps←⋆weaken F.id ⟩
    map TS.weaken (map ⟦_⟧tp← F.id) 
      ≡⟨ cong (map TS.weaken) ⟦id⟧tp← ⟩
    TS.wk ∎
  
  -- the semantics of type weakening is exactly system-f's type weakening
  ⟦wk⟧tp→ : ∀ {n} → map ⟦_⟧tp→ (TS.wk {n}) ≡ F.wk {n}
  ⟦wk⟧tp→ = begin
    map ⟦_⟧tp→ TS.wk 
      ≡⟨ ⟦⟧tps→⋆weaken TS.id ⟩
    map F.weaken (map ⟦_⟧tp→ TS.id) 
      ≡⟨ cong (map F.weaken) ⟦id⟧tp→ ⟩
    F.wk ∎
  
  ⟦⟧tps←⋆↑ :  ∀ {ν n} (v : Vec (F.Type ν) n) → ⟦ v F.↑ ⟧tps← ≡ ⟦ v ⟧tps← TS.↑
  ⟦⟧tps←⋆↑ xs = begin
    (simpl (tvar zero)) ∷ (map ⟦_⟧tp← (map F.weaken xs)) 
      ≡⟨ cong (_∷_ (simpl (tvar zero))) (⟦⟧tps←⋆weaken xs) ⟩
    (simpl (tvar zero)) ∷ (map TS.weaken (map ⟦_⟧tp← xs)) 
      ≡⟨ refl ⟩
    (map ⟦_⟧tp← xs) TS.↑ ∎
  
  ⟦⟧tps→⋆↑ :  ∀ {ν n} (v : Vec (Type ν) n) → ⟦ v TS.↑ ⟧tps→ ≡ ⟦ v ⟧tps→ F.↑
  ⟦⟧tps→⋆↑ xs = begin
    F.tvar zero ∷ (map ⟦_⟧tp→ (map TS.weaken xs)) 
      ≡⟨ cong (_∷_ (F.tvar zero)) (⟦⟧tps→⋆weaken xs) ⟩
    F.tvar zero ∷ (map F.weaken (map ⟦_⟧tp→ xs)) 
      ≡⟨ refl ⟩
    (map ⟦_⟧tp→ xs) F.↑ ∎
  
  -- type substitution commutes with interpreting types
  /⋆⟦⟧tp← : ∀ {ν μ} (tp : F.Type ν) (σ : Sub F.Type ν μ) → ⟦ tp F./ σ ⟧tp← ≡ ⟦ tp ⟧tp← TS./ (map ⟦_⟧tp← σ)
  /⋆⟦⟧tp← (F.tc c) σ = refl
  /⋆⟦⟧tp← (F.tvar n) σ = begin
    ⟦ lookup n σ ⟧tp← 
      ≡⟨ lookup⋆map σ ⟦_⟧tp← n ⟩
    ⟦ F.tvar n ⟧tp← TS./ (map ⟦_⟧tp← σ) ∎
  /⋆⟦⟧tp← (l F.→' r) σ = cong₂ _⇒_ (/⋆⟦⟧tp← l σ) (/⋆⟦⟧tp← r σ)
  /⋆⟦⟧tp← (l F.⟶ r) σ = cong₂ (λ u v → simpl (u →' v)) (/⋆⟦⟧tp← l σ) (/⋆⟦⟧tp← r σ)
  /⋆⟦⟧tp← (F.∀' a) σ = begin
    ∀' ⟦ (a F./ σ F.↑) ⟧tp←
      ≡⟨ cong ∀' (/⋆⟦⟧tp← a (σ F.↑)) ⟩
    ∀' (⟦ a ⟧tp← / ⟦ σ F.↑ ⟧tps←)
      ≡⟨ cong (λ u → ∀' (⟦ a ⟧tp← TS./ u)) ((⟦⟧tps←⋆↑ σ)) ⟩
    ⟦ F.∀' a ⟧tp← / (map ⟦_⟧tp← σ) ∎
  
  -- type substitution commutes with interpreting types
  /⋆⟦⟧tp→ : ∀ {ν μ} (tp : Type ν) (σ : Sub Type ν μ) → ⟦ tp TS./ σ ⟧tp→ ≡ ⟦ tp ⟧tp→ F./ (map ⟦_⟧tp→ σ)
  /⋆⟦⟧tp→ (simpl (tc c)) σ = refl
  /⋆⟦⟧tp→ (simpl (tvar n)) σ = begin
    ⟦ lookup n σ ⟧tp→ 
      ≡⟨ lookup⋆map σ ⟦_⟧tp→ n ⟩
    ⟦ simpl (tvar n) ⟧tp→ F./ (map ⟦_⟧tp→ σ) ∎
  /⋆⟦⟧tp→ (l ⇒ r) σ = cong₂ F._→'_ (/⋆⟦⟧tp→ l σ) (/⋆⟦⟧tp→ r σ)
  /⋆⟦⟧tp→ (simpl (l →' r)) σ = cong₂ F._⟶_ (/⋆⟦⟧tp→ l σ) (/⋆⟦⟧tp→ r σ)
  /⋆⟦⟧tp→ (∀' a) σ = begin
    F.∀' ⟦ (a TS./ σ TS.↑) ⟧tp→
      ≡⟨ cong F.∀' (/⋆⟦⟧tp→ a (σ TS.↑)) ⟩
    F.∀' (⟦ a ⟧tp→ F./ ⟦ σ TS.↑ ⟧tps→)
      ≡⟨ cong (λ u → F.∀' (⟦ a ⟧tp→ F./ u)) ((⟦⟧tps→⋆↑ σ)) ⟩
    ⟦ ∀' a ⟧tp→ F./ (map ⟦_⟧tp→ σ) ∎
  
  ⟦a/sub⟧tp← : ∀ {ν} (a : F.Type (suc ν)) b → ⟦ a F./ (F.sub b) ⟧tp← ≡ ⟦ a ⟧tp← TS./ (TS.sub ⟦ b ⟧tp←)
  ⟦a/sub⟧tp← a b = begin
    ⟦ a F./ (F.sub b) ⟧tp←
    ≡⟨ /⋆⟦⟧tp← a (b ∷ F.id) ⟩
    (⟦ a ⟧tp← TS./ (map ⟦_⟧tp← (b ∷ F.id)) )
    ≡⟨ refl ⟩
    (⟦ a ⟧tp← TS./ (⟦ b ⟧tp← ∷ (map ⟦_⟧tp← F.id)) )
    ≡⟨ cong (λ s → ⟦ a ⟧tp← TS./ (⟦ b ⟧tp← ∷ s)) ⟦id⟧tp← ⟩
    (⟦ a ⟧tp← TS./ (TS.sub ⟦ b ⟧tp←)) ∎
  
  ⟦a/wk⟧tp← : ∀ {ν} → (a : F.Type ν) → ⟦ a F./ F.wk ⟧tp← ≡ ⟦ a ⟧tp← / wk
  ⟦a/wk⟧tp← tp = begin
    ⟦ tp F./ F.wk ⟧tp←
      ≡⟨ /⋆⟦⟧tp← tp F.wk ⟩
    ⟦ tp ⟧tp← / (map ⟦_⟧tp← F.wk) 
      ≡⟨ cong (λ e → ⟦ tp ⟧tp← / e) ⟦wk⟧tp← ⟩
    ⟦ tp ⟧tp← / wk ∎
  
  ⟦a/wk⟧tp→ : ∀ {ν} → (a : Type ν) → ⟦ a / wk ⟧tp→ ≡ ⟦ a ⟧tp→ F./ F.wk
  ⟦a/wk⟧tp→ tp = begin
    ⟦ tp TS./ TS.wk ⟧tp→
      ≡⟨ /⋆⟦⟧tp→ tp TS.wk ⟩
    ⟦ tp ⟧tp→ F./ (map ⟦_⟧tp→ TS.wk) 
      ≡⟨ cong (λ e → ⟦ tp ⟧tp→ F./ e) ⟦wk⟧tp→ ⟩
    ⟦ tp ⟧tp→ F./ F.wk ∎
  
  ⟦weaken⟧ctx← : ∀ {ν n} (Γ : F.Ctx ν n) → ⟦ F.ctx-weaken Γ ⟧ctx← ≡ ictx-weaken ⟦ Γ ⟧ctx←
  ⟦weaken⟧ctx← [] = refl
  ⟦weaken⟧ctx← (x ∷ xs) = begin
    ⟦ F.ctx-weaken (x ∷ xs) ⟧ctx←
      ≡⟨ refl ⟩
    toList (map ⟦_⟧tp← (map (flip F._/_ F.wk) (x ∷ xs)))
      ≡⟨ cong toList (sym (VP.map-∘ _ _ (x ∷ xs))) ⟩
    (⟦ x F./ F.wk ⟧tp← List.∷ (toList (map (⟦_⟧tp← ∘ (flip F._/_ F.wk)) xs)))
      ≡⟨ cong (λ u → ⟦ F._/_ x F.wk ⟧tp← List.∷ toList u) (VP.map-∘ _ _ xs) ⟩
    (⟦ x F./ F.wk ⟧tp← List.∷ ⟦ F.ctx-weaken xs ⟧ctx←)
      ≡⟨ cong (λ u → ⟦ F._/_ x F.wk ⟧tp← List.∷ u) (⟦weaken⟧ctx← xs) ⟩
    (⟦ x F./ F.wk ⟧tp← List.∷ (ictx-weaken ⟦ xs ⟧ctx←))
      ≡⟨ cong (flip List._∷_ (ictx-weaken ⟦ xs ⟧ctx←)) (⟦a/wk⟧tp← x) ⟩
    ictx-weaken ⟦ x ∷ xs ⟧ctx← ∎
  
  ⟦weaken⟧ctx→ : ∀ {ν} (Δ : ICtx ν) → F.ctx-weaken ⟦ Δ ⟧ctx→ H.≅ ⟦ ictx-weaken Δ ⟧ctx→
  ⟦weaken⟧ctx→ List.[] = H.refl
  ⟦weaken⟧ctx→ (x List.∷ xs) = HR.begin
    F.ctx-weaken ⟦ x List.∷ xs ⟧ctx→
      HR.≅⟨ H.refl ⟩
    (⟦ x ⟧tp→ F./ F.wk) ∷ F.ctx-weaken ⟦ xs ⟧ctx→
      HR.≅⟨ ∷-cong (sym (length-weaken-Δ xs)) (⟦weaken⟧ctx→ xs) ⟩
    (⟦ x ⟧tp→ F./ F.wk) ∷ ⟦ ictx-weaken xs ⟧ctx→
      HR.≅⟨ H.cong (flip _∷_ ⟦ ictx-weaken xs ⟧ctx→) (H.≡-to-≅ $ sym $ ⟦a/wk⟧tp→ x) ⟩
    ⟦ x / wk ⟧tp→ ∷ ⟦ ictx-weaken xs ⟧ctx→
      HR.≅⟨ H.cong (λ u → ⟦ x / wk ⟧tp→ ∷ fromList u) (H.≡-to-≅ (sym (map-compose xs))) ⟩
    (fromList (List.map (⟦_⟧tp→ ∘ (λ s → s / wk)) (x List.∷ xs)))
      HR.≅⟨ H.cong fromList (H.≡-to-≅ (map-compose (x List.∷ xs))) ⟩
    ⟦ ictx-weaken (x List.∷ xs) ⟧ctx→ HR.∎
  
  ⟦a/sub⟧tp→ : ∀ {ν} (a : Type (suc ν)) b → ⟦ a TS./ (TS.sub b) ⟧tp→ ≡ ⟦ a ⟧tp→ F./ (F.sub ⟦ b ⟧tp→)
  ⟦a/sub⟧tp→ a b = begin
    ⟦ a TS./ (TS.sub b) ⟧tp→
    ≡⟨ /⋆⟦⟧tp→ a (b ∷ TS.id) ⟩
    (⟦ a ⟧tp→ F./ (map ⟦_⟧tp→ (b ∷ TS.id)) )
    ≡⟨ refl ⟩
    (⟦ a ⟧tp→ F./ (⟦ b ⟧tp→ ∷ (map ⟦_⟧tp→ TS.id)) )
    ≡⟨ cong (λ s → ⟦ a ⟧tp→ F./ (⟦ b ⟧tp→ ∷ s)) ⟦id⟧tp→ ⟩
    (⟦ a ⟧tp→ F./ (F.sub ⟦ b ⟧tp→)) ∎
  
  from : ∀ {ν n t a} {Γ : F.Ctx ν n} → Γ F.⊢ t ∈ a → ⟦ Γ ⟧ctx← ⊢ᵣ ⟦ a ⟧tp←
  from (F.var x) = r-ivar (lem x _)
    where
      lem : ∀ {ν n} → (x : Fin n) → (v : F.Ctx ν n) → ⟦ lookup x v ⟧tp← List.∈ ⟦ v ⟧ctx←
      lem zero (x ∷ xs) = here refl
      lem (suc x) (v ∷ vs) = there (lem x vs) 
  from {Γ = Γ} (F.Λ x) = r-tabs (subst (λ u → u ⊢ᵣ _) (⟦weaken⟧ctx← Γ) (from x))
  from (F.λ' {b = b} a x) = r-iabs (from x)
  from {Γ = Γ} (F._[_] {a = a} x b) = subst
    (λ u → ⟦ Γ ⟧ctx← ⊢ᵣ u)
    (sym (⟦a/sub⟧tp← a b))
    (r-tapp ⟦ b ⟧tp← (from x))
  from (a F.· b) = r-iapp (from a) (from b)
  
  ⊢subst-n : ∀ {ν n n'} {Γ : F.Ctx ν n} {Γ' : F.Ctx ν n'} {t a} → (n-eq : n ≡ n') →
             Γ H.≅ Γ' → Γ F.⊢ t ∈ a →
             Γ' F.⊢ (subst (F.Term ν) n-eq t) ∈ a
  ⊢subst-n refl H.refl p = p
  
  lookup-subst-n : ∀ {n n' l} {A : Set l} {v : Vec A n} {v' : Vec A n'} {i : Fin n} →
                   (n-eq : n ≡ n') →
                   (v H.≅ v') →
                   (lookup i v) ≡ (lookup (subst Fin n-eq i) v')
  lookup-subst-n refl H.refl = refl
  
  lookup⟦⟧ : ∀ {ν} (Δ : ICtx ν) {r} i → lookup i (fromList Δ) ≡ r →
             (lookup (subst Fin (sym $ length-map _ Δ) i) ⟦ Δ ⟧ctx→) ≡ ⟦ r ⟧tp→
  lookup⟦⟧ Δ {r = r} i eq = begin
    (lookup (subst Fin (sym $ length-map _ Δ) i) ⟦ Δ ⟧ctx→)
      ≡⟨ refl ⟩
    (lookup (subst Fin (sym $ length-map _ Δ) i) (fromList $ (List.map ⟦_⟧tp→ Δ)))
      ≡⟨ sym $ lookup-subst-n (sym $ length-map _ Δ) (H.sym $ fromList-map _ Δ) ⟩
    (lookup i (map ⟦_⟧tp→ (fromList Δ)))
      ≡⟨ sym $ lookup⋆map (fromList Δ) ⟦_⟧tp→ i ⟩
    ⟦ lookup i (fromList Δ) ⟧tp→
      ≡⟨ cong ⟦_⟧tp→ eq ⟩
    ⟦ r ⟧tp→ ∎
  
  ⟦_⟧ᵣ : ∀ {ν} {Δ : ICtx ν} {r} → (p : Δ ⊢ᵣ r) → ⟦ Δ ⟧ctx→ F.⊢ ⟦ p ⟧term→ ∈ ⟦ r ⟧tp→
  ⟦_⟧ᵣ {Δ = Δ} (r-tabs {r = r} p) with ⟦ p ⟧ᵣ
  ⟦_⟧ᵣ {Δ = Δ} (r-tabs {r = r} p) | x =
    F.Λ (⊢subst-n (length-weaken-Δ Δ) (H.sym (⟦weaken⟧ctx→ Δ)) x)
  ⟦_⟧ᵣ (r-tapp a p) with ⟦ p ⟧ᵣ
  ⟦_⟧ᵣ {Δ = Δ} (r-tapp {r = a} b p) | x =
    subst
      (λ u → ⟦ Δ ⟧ctx→ F.⊢ ⟦ p ⟧term→ F.[ ⟦ b ⟧tp→ ] ∈ u)
      (sym $ ⟦a/sub⟧tp→ a b)
      (x F.[ ⟦ b ⟧tp→ ])
  ⟦_⟧ᵣ {Δ = Δ} {r = r} (r-ivar x) =
    let i , eq = ∈⟶index (VP.List-∈⇒∈ x) in 
        let i' = (subst Fin (sym $ length-map _ Δ) i) in
          subst (λ u → ⟦ Δ ⟧ctx→ F.⊢ (F.var i') ∈ u) (lookup⟦⟧ Δ i eq) (F.var i')
  ⟦_⟧ᵣ (r-iabs {a = a} p) = F.λ' ⟦ a ⟧tp→ ⟦ p ⟧ᵣ
  ⟦_⟧ᵣ (r-iapp p p₁) = ⟦ p ⟧ᵣ F.· ⟦ p₁ ⟧ᵣ
  
  -- proof that
  iso : ∀ {ν} (Δ : ICtx ν) r → Δ ⊢ᵣ r ⇔ (∃ λ t → ⟦ Δ ⟧ctx→ F.⊢ t ∈ ⟦ r ⟧tp→)
  iso Δ r = equivalence
    (λ x → , ⟦ x ⟧ᵣ)
    (λ x → subst₂ (λ Δ' r' → Δ' ⊢ᵣ r') (ctx→← _) (tp→← r) (from (proj₂ x)))

  
{-
  Assuming undecidability of the type inhabitation problem for System F
  (as proven by e.g. Barendregt) we can prove the undecidability of Ambiguous resolution
-}

private
  -- type of inhabitation problem decider
  ?:-dec : Set
  ?:-dec = ∀ {ν} → (a : F.Type ν) → Dec (∃ λ t → [] F.⊢ t ∈ a)

module Undecidable (?:-undec : ¬ ?:-dec) where

  open Embedding
  open Lemmas

  -- type of decider for ambiguous resolution
  ⊢ᵣ-dec : Set
  ⊢ᵣ-dec = ∀ {ν} (Δ : ICtx ν) → (a : Type ν) → Dec (Δ ⊢ᵣ a)

  -- proof that such a decider would imply a decider for type inhabitation problem
  reduction : ⊢ᵣ-dec → ?:-dec
  reduction f x = Dec.map (
    subst
      (λ u → List.[] ⊢ᵣ ⟦ x ⟧tp← ⇔ ∃ (λ t → [] F.⊢ t ∈ u))
      (tp←→ x)
      (iso List.[] ⟦ x ⟧tp←)) (f List.[] ⟦ x ⟧tp←)

  -- completing the proof
  undecidable : ¬ ⊢ᵣ-dec
  undecidable f = ?:-undec (reduction f) 