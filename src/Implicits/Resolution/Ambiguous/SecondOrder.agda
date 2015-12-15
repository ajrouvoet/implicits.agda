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
open TypeSubst hiding (subst)
module TS = TypeSubst

open import SystemF TC as F using ()

private
  ⟦_⟧tp← : ∀ {ν} → F.Type ν → Type ν
  ⟦ F.tc x ⟧tp← = simpl (tc x)
  ⟦ F.tvar n ⟧tp← = simpl (tvar n)
  ⟦ a F.→' b ⟧tp← = (⟦ a ⟧tp← ⇒ ⟦ b ⟧tp←)
  ⟦ a F.⟶ b ⟧tp← = simpl (⟦ a ⟧tp← →' ⟦ b ⟧tp←)
  ⟦ F.∀' x ⟧tp← = ∀' ⟦ x ⟧tp←

  ⟦_⟧ctx← : ∀ {ν n} → Vec (F.Type ν) n → List (Type ν)
  ⟦ v ⟧ctx← = toList $ map ⟦_⟧tp← v

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
