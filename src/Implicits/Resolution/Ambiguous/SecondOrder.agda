open import Prelude
open import Function.Equivalence using (_⇔_; equivalence)
open import Data.Fin.Substitution
open import Data.List.Properties
open import Relation.Binary.HeterogeneousEquality as H using ()
module HR = H.≅-Reasoning
open import Data.Vec.Properties as VP using ()

module Implicits.Resolution.Ambiguous.SecondOrder TC _tc≟_ where

open import Implicits.Syntax TC _tc≟_
open import Implicits.Resolution.Ambiguous.Resolution TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open import Implicits.Substitutions.Lemmas TC _tc≟_
open import Implicits.Resolution.Ambiguous.Semantics TC _tc≟_
open TypeSubst hiding (subst)

private
  module TS = TypeSubst

open import SystemF TC as F using ()

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

tp→← : ∀ {ν} (a : Type ν) → ⟦ ⟦ a ⟧tp→ ⟧tp← ≡ a
tp→← (simpl (tc x)) = refl
tp→← (simpl (tvar n)) = refl
tp→← (simpl (x →' x₁)) = cong₂ (λ u v → simpl (u →' v)) (tp→← x) (tp→← x₁)
tp→← (a ⇒ b) = cong₂ _⇒_ (tp→← a) (tp→← b)
tp→← (∀' a) = cong ∀' (tp→← a)

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

⟦weaken⟧tp← : ∀ {ν} (a : F.Type ν) → ⟦ F.weaken a ⟧tp← ≡ weaken ⟦ a ⟧tp←
⟦weaken⟧tp← x = ⟦a/var⟧tp← x VarSubst.wk

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

-- the semantics of type weakening is exactly system-f's type weakening
⟦wk⟧tp← : ∀ {n} → map ⟦_⟧tp← (F.wk {n}) ≡ TS.wk {n}
⟦wk⟧tp← = begin
  map ⟦_⟧tp← F.wk 
    ≡⟨ ⟦⟧tps←⋆weaken F.id ⟩
  map TS.weaken (map ⟦_⟧tp← F.id) 
    ≡⟨ cong (map TS.weaken) ⟦id⟧tp← ⟩
  TS.wk ∎

⟦⟧tps←⋆↑ :  ∀ {ν n} (v : Vec (F.Type ν) n) → ⟦ v F.↑ ⟧tps← ≡ ⟦ v ⟧tps← TS.↑
⟦⟧tps←⋆↑ xs = begin
  (simpl (tvar zero)) ∷ (map ⟦_⟧tp← (map F.weaken xs)) 
    ≡⟨ cong (_∷_ (simpl (tvar zero))) (⟦⟧tps←⋆weaken xs) ⟩
  (simpl (tvar zero)) ∷ (map TS.weaken (map ⟦_⟧tp← xs)) 
    ≡⟨ refl ⟩
  (map ⟦_⟧tp← xs) TS.↑ ∎

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

iso : ∀ {ν} {Δ : ICtx ν} r → Δ ⊢ᵣ r ⇔ (∃ λ t → ⟦ Δ ⟧ctx→ F.⊢ t ∈ ⟦ r ⟧tp→)
iso r = equivalence
  (λ x → , ⟦ x ⟧ᵣ)
  (λ x → subst₂ (λ Δ' r' → Δ' ⊢ᵣ r') (ctx→← _) (tp→← r) (from (proj₂ x)))
