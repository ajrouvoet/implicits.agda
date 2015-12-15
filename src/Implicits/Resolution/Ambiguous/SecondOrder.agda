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

⟦a[/b]⟧tp← : ∀ {ν} (a : F.Type (suc ν)) b → ⟦ a F./ (F.sub b) ⟧tp← ≡ ⟦ a ⟧tp← / (sub ⟦ b ⟧tp←)
⟦a[/b]⟧tp← tp = {!!}

⟦weaken⟧ctx← : ∀ {ν n} (Γ : F.Ctx ν n) → ⟦ F.ctx-weaken Γ ⟧ctx← ≡ ictx-weaken ⟦ Γ ⟧ctx←
⟦weaken⟧ctx← = {!!}

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
  (sym (⟦a[/b]⟧tp← a b))
  (r-tapp ⟦ b ⟧tp← (from x))
from (a F.· b) = r-iapp (from a) (from b)

iso : ∀ {ν} {Δ : ICtx ν} r → Δ ⊢ᵣ r ⇔ (∃ λ t → ⟦ Δ ⟧ctx→ F.⊢ t ∈ ⟦ r ⟧tp→)
iso r = equivalence
  (λ x → , ⟦ x ⟧ᵣ)
  (λ x → subst₂ (λ Δ' r' → Δ' ⊢ᵣ r') (ctx→← _) (tp→← r) (from (proj₂ x)))
