module LFRef.Eval where

open import Prelude
open import Data.Fin using (fromℕ≤)
open import Data.List hiding ([_])
open import Data.List.All
open import Data.List.Any
open import Data.Vec hiding (map; _∷ʳ_)
open import Data.Maybe hiding (All; Any)
open import Extensions.List as L

open import LFRef.Syntax hiding (subst)
open import LFRef.Welltyped

-- machine configuration: expression to reduce and a store
Config : Set
Config = Exp 0 × Store

!load : ∀ {i} → (μ : Store) → i < length μ → Term 0
!load {i = i} [] ()
!load {i = zero} (x ∷ μ) (s≤s p) = proj₁ x
!load {i = suc i} (x ∷ μ) (s≤s p) = !load μ p

!store : ∀ {i e} → (μ : Store) → i < length μ → Val e → Store
!store [] () v
!store {i = zero} (x ∷ μ) (s≤s p) v = (, v) ∷ μ
!store {i = suc i} (x ∷ μ) (s≤s p) v = (, v) ∷ (!store μ p v)

!call : ∀ {n m} → Exp m → (l : List (Term n)) → length l ≡ m → Exp n
!call e ts p = e exp/ subst (Vec _) p (fromList ts)

-- small steps for expressions
infix 1 _⊢_≻_
data _⊢_≻_ (𝕊 : Sig) : (t t' : Config) → Set where

  funapp-β : ∀ {fn ts μ φ} →
             (Sig.funs 𝕊) L.[ fn ]= φ →
             (p : length ts ≡ Fun.m φ) →
             -------------------------
             𝕊 ⊢ fn ·★ ts , μ ≻ (!call (Fun.body φ) ts p) , μ

  ref-val : ∀ {t μ} →
            (v : Val t) →
            ----------------------------------------------------
            𝕊 ⊢ ref (tm t) , μ ≻ (tm (loc (length μ))) , (μ ∷ʳ (, v))

  ≔-val : ∀ {i e μ} →
          (p : i < length μ) →
          (v : Val e) →
          --------------------------------------------
          𝕊 ⊢ (tm (loc i)) ≔ (tm e) , μ ≻ (tm unit) , (μ L.[ fromℕ≤ p ]≔ (, v))

  !-val : ∀ {i μ} →
          (p : i < length μ) →
          -----------------------------------------
          𝕊 ⊢ ! (tm (loc i)) , μ ≻ tm (!load μ p) , μ


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
             ExpVal x →
             𝕊 ⊢ e , μ ≻ e' , μ' →
             --------------------------
             𝕊 ⊢ x ≔ e , μ ≻ x ≔ e' , μ'

infix 1 _⊢_≻ₛ_
data _⊢_≻ₛ_ (𝕊 : Sig) : (t t' : SeqExp 0 × Store) → Set where

  -- reductions
  lett-β  : ∀ {t e μ} →
            ----------------------------------------------
            𝕊 ⊢ (lett (tm t) e) , μ ≻ₛ (e seq/ (sub t)) , μ

  -- contextual closure
  ret-clos  : ∀ {e μ e' μ'} →
              𝕊 ⊢ e , μ ≻ e' , μ' →
              -------------------------------------
              𝕊 ⊢ (ret e) , μ ≻ₛ (ret e') , μ'

  lett-clos : ∀ {x e x' μ μ'} →
              𝕊 ⊢ x , μ ≻ x' , μ' →
              -------------------------------------
              𝕊 ⊢ (lett x e) , μ ≻ₛ (lett x' e) , μ'

-- reflexive-transitive closure of ≻
open import Data.Star
_⊢_≻⋆_ : (Sig) → (c c' : Config) → Set
𝕊 ⊢ c ≻⋆ c' = Star (_⊢_≻_ 𝕊) c c'
