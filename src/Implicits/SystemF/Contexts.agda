module Implicits.SystemF.Contexts where

open import Prelude
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Vec.Properties
open import Implicits.SystemF.Types
import Category.Applicative.Indexed as Applicative
open Applicative.Morphism using (op-<$>)

Ctx : ℕ → ℕ → Set
Ctx ν n = Vec (Type ν) n

module CtxSubst where
  
  _/_ : ∀ {ν μ n} → Ctx ν n → Sub Type ν μ → Ctx μ n
  Γ / σ = Γ TypeSubst.⊙ σ
  
  weaken : ∀ {ν n} → Ctx ν n → Ctx (suc ν) n
  weaken Γ = Γ / TypeSubst.wk

  -- Variable substitution (renaming) lifted to typing contexts
  _/Var_ : ∀ {ν m k} → Sub Fin k m → Ctx ν m → Ctx ν k
  σ /Var Γ = map (λ x → lookup x Γ) σ

open CtxSubst public using () renaming (_/_ to _ctx/_; weaken to ctx-weaken; _/Var_ to _ctx/Var_)


module CtxLemmas where
  open CtxSubst public

  private module Tp  = TypeLemmas
  private module Var = VarSubst

  -- Term variable substitution (renaming) commutes with type
  -- substitution.
  /Var-/ : ∀ {m ν n l} (ρ : Sub Fin m n) (Γ : Ctx ν n) (σ : Sub Type ν l) →
           (ρ /Var Γ) / σ ≡ ρ /Var (Γ / σ)
  /Var-/ ρ Γ σ = begin
      (ρ /Var Γ) / σ
    ≡⟨ sym (map-∘ _ _ ρ) ⟩
      map (λ x → (lookup x Γ) Tp./ σ) ρ
    ≡⟨ map-cong (λ x → sym (Tp.lookup-⊙ x)) ρ ⟩
      map (λ x → lookup x (Γ / σ)) ρ
    ∎

  -- Term variable substitution (renaming) commutes with weakening of
  -- typing contexts with an additional type variable.
  /Var-weaken : ∀ {m n k} (ρ : Sub Fin m k) (Γ : Ctx n k) →
                weaken (ρ /Var Γ) ≡ ρ /Var (weaken Γ)
  /Var-weaken ρ Γ = begin
    (ρ /Var Γ) / Tp.wk   ≡⟨ /Var-/ ρ Γ Tp.wk ⟩
    ρ /Var (weaken Γ)    ∎

  -- Term variable substitution (renaming) commutes with term variable
  -- lookup in typing context.
  /Var-lookup : ∀ {m n k} (x : Fin m) (ρ : Sub Fin m k) (Γ : Ctx n k) →
                lookup x (ρ /Var Γ) ≡ lookup (lookup x ρ) Γ
  /Var-lookup x ρ Γ = op-<$> (lookup-morphism x) _ _

  -- Term variable substitution (renaming) commutes with weakening of
  -- typing contexts with an additional term variable.
  /Var-∷ : ∀ {m n k} (a : Type n) (ρ : Sub Fin m k) (Γ : Ctx n k) →
           a ∷ (ρ /Var Γ) ≡ (ρ Var.↑) /Var (a ∷ Γ)
  /Var-∷ a []      Γ = refl
  /Var-∷ a (x ∷ ρ) Γ = cong (_∷_ a) (cong (_∷_ (lookup x Γ)) (begin
    map (λ x → lookup x Γ) ρ                   ≡⟨ refl ⟩
    map (λ x → lookup (suc x) (a ∷ Γ)) ρ       ≡⟨ map-∘ _ _ ρ ⟩
    map (λ x → lookup x (a ∷ Γ)) (map suc ρ)   ∎))

  -- Invariants of term variable substitution (renaming)
  idVar-/Var   : ∀ {m n} (Γ : Ctx n m) → Γ ≡ (Var.id /Var Γ)
  wkVar-/Var-∷ : ∀ {m n} (Γ : Ctx n m) (a : Type n) → Γ ≡ (Var.wk /Var (a ∷ Γ))

  idVar-/Var []      = refl
  idVar-/Var (a ∷ Γ) = cong (_∷_ a) (wkVar-/Var-∷ Γ a)

  wkVar-/Var-∷ Γ a = begin
    Γ ≡⟨ idVar-/Var Γ ⟩
    Var.id /Var Γ ≡⟨ map-∘ _ _ VarSubst.id ⟩
    Var.wk /Var (a ∷ Γ) ∎
  
  ctx-weaken-sub-vanishes : ∀ {ν n} {Γ : Ctx ν n} {a} → (ctx-weaken Γ) ctx/ (Tp.sub a) ≡ Γ
  ctx-weaken-sub-vanishes {Γ = Γ} {a} = begin
    (Γ ctx/ Tp.wk) ctx/ (Tp.sub a) 
      ≡⟨ sym $ map-∘ (λ s → s tp/tp Tp.sub a) (λ s → s tp/tp Tp.wk) Γ ⟩
    (map (λ s → s tp/tp Tp.wk tp/tp (Tp.sub a)) Γ) 
      ≡⟨ map-cong (TypeLemmas.wk-sub-vanishes) Γ ⟩
    (map (λ s → s) Γ) ≡⟨ map-id Γ ⟩
    Γ ∎
