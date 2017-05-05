module LFRef.Eval where

open import Prelude
open import Data.List hiding ([_])
open import Data.List.All
open import Data.List.Any
open import Data.Maybe hiding (All; Any)
open import Extensions.List as L

open import LFRef.Syntax
open import LFRef.Welltyped

-- machine configuration: expression to reduce and a store
Config : ℕ → Set
Config n = Exp n × Store n

!load : ∀ {n i} → (μ : Store n) → i < length μ → Term n
!load {i = i} [] ()
!load {i = zero} (x ∷ μ) (s≤s p) = x
!load {i = suc i} (x ∷ μ) (s≤s p) = !load μ p


!store : ∀ {n i} → (μ : Store n) → i < length μ → Term n → Store n
!store [] () v
!store {i = zero} (x ∷ μ) (s≤s p) v = v ∷ μ
!store {i = suc i} (x ∷ μ) (s≤s p) v = v ∷ (!store μ p v)

!call : ∀ {n es} → (𝕊 : Sig n) → ℕ → All (Val {n}) es → Maybe (Exp n)
!call 𝕊 n p with L.lookup n (Sig.funs 𝕊)
!call 𝕊 n p | yes ((φ , e) , _) = just e
!call 𝕊 n p | no _ = nothing

-- small steps for expressions
infix 1 _⊢_≻_
data _⊢_≻_ {n} (𝕊 : Sig n) : (t t' : Config n) → Set where

  -- reductions
  lett-β  : ∀ {t e μ} →
            ----------------------------------------------
            𝕊 ⊢ (lett (tm t) e) , μ ≻ (e exp/ (sub t)) , μ

  funapp-β : ∀ {fn es μ e'} →
             (p : All Val es) →
             !call 𝕊 fn p ≡ just e' →
             -------------------------
             𝕊 ⊢ fn ·★ es , μ ≻ e' , μ

  ref-val : ∀ {t μ} →
            ----------------------------------------------------
            𝕊 ⊢ ref (tm t) , μ ≻ (tm (loc (length μ))) , (μ ∷ʳ t)

  ≔-val : ∀ {i x t μ} →
          (p : i < length μ) →
          --------------------------------------------
          𝕊 ⊢ tm x ≔ (tm t) , μ ≻ (tm unit) , !store μ p t

  !-val : ∀ {i x μ} →
          (p : i < length μ) →
          -----------------------------------------
          𝕊 ⊢ ! (tm x) , μ ≻ tm (!load μ p) , μ

  -- contextual closure
  lett-clos : ∀ {x e x' μ μ'} →
              𝕊 ⊢ x , μ ≻ x' , μ' →
              -------------------------------------
              𝕊 ⊢ (lett x e) , μ ≻ (lett x' e) , μ'

  fun-clos : ∀ {fn es e' μ μ'} →
             (p : Any (λ e → 𝕊 ⊢ e , μ ≻ e' , μ') es) →
             ------------------------------------------------------
             𝕊 ⊢ (fn ·★ es) , μ ≻ (fn ·★ (es [ index p ]≔ e')) , μ'

  ref-clos : ∀ {e e' μ μ'} →
             𝕊 ⊢ e , μ ≻ e' , μ' →
             ---------------------------
             𝕊 ⊢ ref e , μ ≻ ref e' , μ'

  !-clos   : ∀ {e e' μ μ'} →
             𝕊 ⊢ e , μ ≻ e' , μ' →
             -----------------------
             𝕊 ⊢ ! e , μ ≻ ! e' , μ'

  ≔-clos₁  : ∀ {x x' e μ μ'} →
             𝕊 ⊢ x , μ ≻ x' , μ' →
             --------------------------
             𝕊 ⊢ x ≔ e , μ ≻ x' ≔ e , μ'

  ≔-clos₂  : ∀ {x e e' μ μ'} →
             𝕊 ⊢ e , μ ≻ e' , μ' →
             --------------------------
             𝕊 ⊢ x ≔ e , μ ≻ x ≔ e' , μ'

-- Church-Rosser
-- diamond : ∀ {n} {u u' u'' : Term n} → u ≻ u' → u ≻ u'' → ∃ λ v → (u' ≻ v × u'' ≻ v)
-- church-rosser : ∀ {n} {u u' u'' : Term n} → u ≻⋆ u' → u ≻⋆ u'' → ∃ λ v → (u' ≻⋆ v × u'' ≻⋆ v)

-- reflexive-transitive closure of ≻
open import Data.Star
_⊢_≻⋆_ : ∀ {n} → (Sig n) → (c c' : Config n) → Set
𝕊 ⊢ c ≻⋆ c' = Star (_⊢_≻_ 𝕊) c c'
