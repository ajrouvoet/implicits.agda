module LFRef.Welltyped where

open import Prelude

open import Data.List hiding ([_])
open import Data.Vec as Vec hiding ([_])
open import Data.Star hiding (_▻▻_)
open import Data.Sum
open import Extensions.List as L using ()

open import LFRef.Syntax
open import Relation.Binary.List.Pointwise using (Rel)

Sig : ℕ → Set
Sig n = List (Kind n) × List (Type n)

Ctx : (n : ℕ) → Set
Ctx n = Vec (Type n) n

-- store typings
World : ℕ → Set
World n = List (Type n)

postulate
  _:+:_ : ∀ {n} → Type n → Ctx n → Ctx (suc n)
  weaken-𝕊 : ∀ {n} → Sig n → Sig (suc n)
  weaken-Σ : ∀ {n} → World n → World (suc n)
  weaken-tp : ∀ {n} → Type n → Type (suc n)

-- mutually inductive welltypedness judgments for kinds/types and terms respectively
data _,_,_⊢_ok : ∀ {n} → (𝕊 : Sig n) → World n → Ctx n → Kind n → Set
data _,_,_⊢_::_ : ∀ {n} (𝕊 : Sig n) → World n → Ctx n → Type n → Kind n → Set
data _,_,_⊢_∶_ : ∀ {n} (𝕊 : Sig n) → World n → Ctx n → Term n → Type n → Set

data _,_,_⊢_ok where

  ★ : ∀ {n 𝕊 Σ} {Γ : Ctx n} →
      ---------------------------------
      𝕊 , Σ , Γ ⊢ ★ ok
  Π : ∀ {n 𝕊 Σ} {Γ : Ctx n} {A K} →
      𝕊 , Σ , Γ ⊢ A :: ★ →
      weaken-𝕊 𝕊 , weaken-Σ Σ , (A :+: Γ) ⊢ K ok →
      ---------------------------------
      𝕊 , Σ , Γ ⊢ Π A K ok

data _,_,_⊢_::_ where

  𝕜 : ∀ {n 𝕊 Σ} {Γ : Ctx n} {i K} →
      proj₁ 𝕊 L.[ i ]= K →
      ---------------------------------
      𝕊 , Σ , Γ ⊢ K ok → 𝕊 , Σ , Γ ⊢ 𝕜 i :: K

  Π : ∀ {n 𝕊 Σ} {Γ : Ctx n} {A B} →
      𝕊 , Σ , Γ ⊢ A :: ★ →
      weaken-𝕊 𝕊 , weaken-Σ Σ , (A :+: Γ) ⊢ B :: ★ →
      ---------------------------------
      𝕊 , Σ , Γ ⊢ Π A B :: ★

  _[_] : ∀ {n 𝕊 Σ} {Γ : Ctx n} {A x S K} →
         𝕊 , Σ , Γ ⊢ S :: (Π A K) →
         𝕊 , Σ , Γ ⊢ x ∶ A →
         ---------------------------------
         𝕊 , Σ , Γ ⊢ S [ x ] :: (K kind/ (sub x))

data _,_,_⊢_∶_ where

  unit : ∀ {n 𝕊 Σ} {Γ : Ctx n} →
        ---------------------------------
        𝕊 , Σ , Γ ⊢ unit ∶ Unit

  var : ∀ {n 𝕊 Σ} {Γ : Ctx n} {i A} →
        Γ [ i ]= A →
        ---------------------------------
        𝕊 , Σ , Γ ⊢ var i ∶ A

  con : ∀ {n 𝕊 Σ} {Γ : Ctx n} {i S} →
        (proj₂ 𝕊) L.[ i ]= S →
        ---------------------------------
        𝕊 , Σ , Γ ⊢ con i ∶ S

  loc : ∀ {n 𝕊 Σ} {Γ : Ctx n} {i S} →
        Σ L.[ i ]= S →
        ---------------------------------
        𝕊 , Σ , Γ ⊢ loc i ∶ S

  ƛ : ∀ {n 𝕊 Σ} {Γ : Ctx n} {x A B} →
      𝕊 , Σ , Γ ⊢ A :: ★ →
      weaken-𝕊 𝕊 , weaken-Σ Σ , (A :+: Γ) ⊢ x ∶ B →
      ---------------------------------
      𝕊 , Σ , Γ ⊢ ƛ A x ∶ Π A B

  _·_ : ∀ {n 𝕊 Σ} {Γ : Ctx n} {f e A B} →
        𝕊 , Σ , Γ ⊢ f ∶ Π A B →
        𝕊 , Σ , Γ ⊢ e ∶ A →
        𝕊 , Σ , Γ ⊢ f · e ∶ (B tp/ (sub e))

data _,_,_⊢ₑ_∶_ : ∀ {n} (𝕊 : Sig n) → World n → Ctx n → Exp n → Type n → Set where

  tm   : ∀ {n t} {Γ : Ctx n} {𝕊 Σ A} →
         𝕊 , Σ , Γ ⊢ t ∶ A →
         -----------------
         𝕊 , Σ , Γ ⊢ₑ tm t ∶ A

  lett : ∀ {n x c A B 𝕊 Σ} {Γ : Ctx n} →
         𝕊 , Σ , Γ ⊢ₑ x ∶ A →
         (weaken-𝕊 𝕊) , (weaken-Σ Σ) , (A :+: Γ) ⊢ₑ c ∶ weaken-tp B →
         ---------------------------------------------
         𝕊 , Σ , Γ ⊢ₑ lett x c ∶ B

  ref : ∀ {n x A 𝕊 Σ} {Γ : Ctx n} →
        𝕊 , Σ , Γ ⊢ₑ x ∶ A →
        ---------------------------------------
        𝕊 , Σ , Γ ⊢ₑ ref x ∶ Ref A

  !_  : ∀ {n x A} {Γ : Ctx n} {𝕊 Σ} →
        𝕊 , Σ , Γ ⊢ₑ x ∶ Ref A →
        ---------------------------------------
        𝕊 , Σ , Γ ⊢ₑ (! x) ∶ A

  _≔_ : ∀ {n i x A} {Γ : Ctx n} {𝕊 Σ} →
        𝕊 , Σ , Γ ⊢ₑ i ∶ Ref A →
        𝕊 , Σ , Γ ⊢ₑ x ∶ A →
        ---------------------------------------
        𝕊 , Σ , Γ ⊢ₑ (i ≔ x) ∶ Unit

-- store welltypedness relation
-- as a pointwise lifting of the welltyped relation on closed expressions between a world and a store
_,_,_⊢_ : ∀ {n} → Sig n → World n → Ctx n → Store n → Set
𝕊 , Σ , Γ ⊢ μ = Rel (λ A x → 𝕊 , Σ , Γ ⊢ x ∶ A) Σ μ
