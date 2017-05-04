module LF.Welltyped where

open import Prelude

open import Data.List hiding ([_])
open import Data.Vec as Vec hiding ([_])
open import Data.Star hiding (_▻▻_)
open import Data.Sum
open import Extensions.List as L using ()

open import LF.Syntax

-- store typings
World : ℕ → Set
World n = List (Type n)

Sig : ℕ → Set
Sig n = List (Kind n) × List (Type n)

Ctx : (n : ℕ) → Set
Ctx n = Vec (Type n) n

postulate
  _:+:_ : ∀ {n} → Type n → Ctx n → Ctx (suc n)
  weaken-Σ : ∀ {n} → Sig n → Sig (suc n)
  weaken-tp : ∀ {n} → Type n → Type (suc n)

-- mutually inductive welltypedness judgments for kinds/types and terms respectively
data _,_⊢_ok : ∀ {n} → (Σ : Sig n) → Ctx n → Kind n → Set
data _,_⊢_::_ : ∀ {n} (Σ : Sig n) → Ctx n → Type n → Kind n → Set
data _,_⊢_∶_ : ∀ {n} (Σ : Sig n) → Ctx n → Term n → Type n → Set

data _,_⊢_ok where

  ★ : ∀ {n Σ} {Γ : Ctx n} →
      ---------------------------------
      Σ , Γ ⊢ ★ ok
  Π : ∀ {n Σ} {Γ : Ctx n} {A K} →
      Σ , Γ ⊢ A :: ★ →
      weaken-Σ Σ , (A :+: Γ) ⊢ K ok →
      ---------------------------------
      Σ , Γ ⊢ Π A K ok

data _,_⊢_::_ where

  𝕜 : ∀ {n Σ} {Γ : Ctx n} {i K} →
      proj₁ Σ L.[ i ]= K →
      ---------------------------------
      Σ , Γ ⊢ K ok → Σ , Γ ⊢ 𝕜 i :: K

  Π : ∀ {n Σ} {Γ : Ctx n} {A B} →
      Σ , Γ ⊢ A :: ★ →
      weaken-Σ Σ , (A :+: Γ) ⊢ B :: ★ →
      ---------------------------------
      Σ , Γ ⊢ Π A B :: ★

  _[_] : ∀ {n Σ} {Γ : Ctx n} {A x S K} →
         Σ , Γ ⊢ S :: (Π A K) →
         Σ , Γ ⊢ x ∶ A →
         ---------------------------------
         Σ , Γ ⊢ S [ x ] :: (K kind/ (sub x))

data _,_⊢_∶_ where

  var : ∀ {n Σ} {Γ : Ctx n} {i A} →
        Γ [ i ]= A →
        ---------------------------------
        Σ , Γ ⊢ var i ∶ A

  con : ∀ {n Σ} {Γ : Ctx n} {i S} →
        (proj₂ Σ) L.[ i ]= S →
        ---------------------------------
        Σ , Γ ⊢ con i ∶ S

  ƛ : ∀ {n Σ} {Γ : Ctx n} {x A B} →
      Σ , Γ ⊢ A :: ★ →
      weaken-Σ Σ , (A :+: Γ) ⊢ x ∶ B →
      ---------------------------------
      Σ , Γ ⊢ ƛ A x ∶ Π A B

  _·_ : ∀ {n Σ} {Γ : Ctx n} {f e A B} →
        Σ , Γ ⊢ f ∶ Π A B →
        Σ , Γ ⊢ e ∶ A →
        Σ , Γ ⊢ f · e ∶ (B tp/ (sub e))

data _,_⊢ₑ_∶_ : ∀ {n} (Σ : Sig n) → Ctx n → Exp n → Type n → Set where

  tm   : ∀ {n t} {Γ : Ctx n} {Σ A} →
         Σ , Γ ⊢ t ∶ A →
         -----------------
         Σ , Γ ⊢ₑ tm t ∶ A

  lett : ∀ {n x c A B Σ} {Γ : Ctx n} →
         Σ , Γ ⊢ₑ x ∶ A →
         (weaken-Σ Σ) , (A :+: Γ) ⊢ₑ c ∶ weaken-tp B →
         ---------------------------------------------
         Σ , Γ ⊢ₑ lett x c ∶ B

  ref : ∀ {n x A Σ} {Γ : Ctx n} →
        Σ , Γ ⊢ₑ x ∶ A →
        ---------------------------------------
        Σ , Γ ⊢ₑ ref x ∶ Ref A

  !_  : ∀ {n x A} {Γ : Ctx n} {Σ} →
        Σ , Γ ⊢ₑ x ∶ Ref A →
        ---------------------------------------
        Σ , Γ ⊢ₑ (! x) ∶ A

  _≔_ : ∀ {n i x A} {Γ : Ctx n} {Σ} →
        Σ , Γ ⊢ₑ i ∶ Ref A →
        Σ , Γ ⊢ₑ x ∶ A →
        ---------------------------------------
        Σ , Γ ⊢ₑ (i ≔ x) ∶ Unit
