module STLCRef.Properties.Soundness where

open import Data.Nat
open import Data.Sum
open import Data.Product as Pr
open import Data.List
open import Data.Vec hiding (_∷ʳ_)
open import Data.Star
open import Function
open import Extensions.List

open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.Core using (REL; Reflexive)
open import Relation.Binary.List.Pointwise hiding (refl)

open import STLCRef.Syntax hiding (id)
open import STLCRef.Welltyped
open import STLCRef.Eval

ref-value-lemma : ∀ {n A Γ Σ} {e : Exp n} → Γ , Σ ⊢ e ∶ Ref A → Val e → ∃ λ i → e ≡ (loc i)
ref-value-lemma (var x) ()
ref-value-lemma (loc p) (loc i) = i , refl
ref-value-lemma (p · p₁) ()
ref-value-lemma (ref p) ()
ref-value-lemma (! p) ()

progress : ∀ {Γ Σ A} {e : Exp 0} {μ} →
           Γ , Σ ⊢ μ →
           Γ , Σ ⊢ e ∶ A →
           --------------------------------------
           Val e ⊎ ∃₂ λ e' μ' → (e , μ ≻ e' , μ')

progress p unit = inj₁ unit
progress p (var ())

progress p (loc {i = i} q) = inj₁ (loc i)

progress p (ƛ wt) = inj₁ (ƛ _ _)

progress p (f · e) with progress p f
progress p (() · e) | inj₁ unit
progress p (() · e) | inj₁ (loc i)
progress p (ƛ f · e) | inj₁ (ƛ _ _) = inj₂ (_ , (_ , AppAbs))
progress p (f · e) | inj₂ (_ , _ , f≻f') = inj₂ (_ , (_ , (Appₗ f≻f')))

progress p (ref wt) with progress p wt
progress p (ref wt) | inj₁ v = inj₂ (_ , (_ , (RefVal v)))
progress p (ref wt) | inj₂ (_ , _ , wt≻wt') = inj₂ (_ , _ , Ref wt≻wt')

progress p (! wt) with progress p wt
progress p (! wt) | inj₁ v with ref-value-lemma wt v
progress p (! loc q) | inj₁ (loc .i) | (i , refl) =
  inj₂ (_ , (_ , (DerefLoc (P.subst (_<_ _) (pointwise-length p) ([-]=-length q)))))
progress p (! wt) | inj₂ (_ , _ , wt≻wt') = inj₂ (_ , (_ , (Deref wt≻wt')))

progress p (wt ≔ x) with progress p wt | progress p x
progress p (wt ≔ x) | _ | inj₂ (_ , _ , x≻x') = inj₂ (_ , (_ , (Assign₂ x≻x')))
progress p (wt ≔ x) | inj₂ (_ , _ , wt≻wt') | _ = inj₂ (_ , _ , Assign₁ wt≻wt')
progress p (wt ≔ x) | inj₁ v | inj₁ w with ref-value-lemma wt v
progress p (loc q ≔ x) | inj₁ (loc .i) | inj₁ w | (i , refl) =
  inj₂ (_ , (_ , Assign (P.subst (_<_ _) (pointwise-length p) ([-]=-length q)) w))

-- extending the store preserves location typings
⊒-loctype : ∀ {Σ Σ' A} {i} → Σ' ⊒ Σ → Σ ⊢loc i ∶ A → Σ' ⊢loc i ∶ A
⊒-loctype [] ()
⊒-loctype (x ∷ ext) here = here
⊒-loctype (x ∷ ext) (there p) = there (⊒-loctype ext p)

postulate
  sub-preserves : ∀ {n Γ Σ A B x} {e : Exp (suc n)} →
    (B ∷ Γ) , Σ ⊢ e ∶ A →
    Γ , Σ ⊢ x ∶ B →
    Γ , Σ ⊢ (e / sub x) ∶ A

∷ʳ⊢loc : ∀ Σ {A} → (Σ ∷ʳ A) ⊢loc (length Σ) ∶ A
∷ʳ⊢loc [] = here
∷ʳ⊢loc (x ∷ Σ) = there (∷ʳ⊢loc Σ)

!!-loc : ∀ {n Σ Σ' A μ i} {Γ : Ctx n} →
         Rel (λ A x → Γ , Σ ⊢ proj₁ x ∶ A) Σ' μ →
         Σ' ⊢loc i ∶ A → (l : i < length μ) → Γ , Σ ⊢ proj₁ (μ !! l) ∶ A
!!-loc [] ()
!!-loc (x∼y ∷ p) here (s≤s z≤n) = x∼y
!!-loc (x∼y ∷ p) (there q) (s≤s l) = !!-loc p q l

-- extending the store preserves expression typings
⊒-preserves : ∀ {n Γ Σ Σ' A} {e : Exp n} → Σ' ⊒ Σ → Γ , Σ ⊢ e ∶ A → Γ , Σ' ⊢ e ∶ A
⊒-preserves ext unit = unit
⊒-preserves ext (var x) = var x
⊒-preserves ext (loc x) = loc (⊒-loctype ext x)
⊒-preserves ext (ƛ p) = ƛ (⊒-preserves ext p)
⊒-preserves ext (p · q) = (⊒-preserves ext p) · ⊒-preserves ext q
⊒-preserves ext (ref p) = ref (⊒-preserves ext p)
⊒-preserves ext (! p) = ! (⊒-preserves ext p)
⊒-preserves ext (p ≔ q) = (⊒-preserves ext p) ≔ (⊒-preserves ext q)

≻-preserves : ∀ {n Γ Σ A} {e : Exp n} {e' μ' μ} →
              Γ , Σ ⊢ e ∶ A →
              Γ , Σ ⊢ μ → e , μ ≻ e' , μ' →
              ---------------------------------
              ∃ λ Σ' → Γ , Σ' ⊢ e' ∶ A × Σ' ⊒ Σ × Γ , Σ' ⊢ μ'

≻-preserves unit p ()
≻-preserves (var x) p ()
≻-preserves (loc p) p₁ ()
≻-preserves (ƛ wt) p ()

≻-preserves {Σ = Σ} (ƛ wt · wt₁) p AppAbs = Σ , sub-preserves wt wt₁ , ⊑-refl , p
≻-preserves {Σ = Σ} (ref {x = x} {A} wt) p (RefVal v) =
  Σ ∷ʳ A ,
    loc (P.subst (λ i → _ ⊢loc i ∶ _) (pointwise-length p) (∷ʳ⊢loc Σ)) ,
    ∷ʳ-⊒ A Σ ,
    {!!}
≻-preserves {Σ = Σ₁} (! loc x) p (DerefLoc l) = Σ₁ , !!-loc p x l , ⊑-refl , p
≻-preserves {Σ = Σ₁} (loc x ≔ y) p (Assign l v) = Σ₁ , unit , ⊑-refl , {!!}

-- contextual closure
≻-preserves {Σ = Σ} (wt-f · wt-x) p (Appₗ r) =
  Pr.map
    id
    (λ{ (wt-f' , ext , q) → wt-f' · ⊒-preserves ext wt-x , ext , q})
    (≻-preserves wt-f p r)
≻-preserves (f · x) p (Appᵣ r) =
  Pr.map
    id
    (λ{ (x' , ext , q) → ⊒-preserves ext f · x' , ext , q})
    (≻-preserves x p r)
≻-preserves (ref wt) p (Ref r) = Pr.map id (λ{ (wt' , ext) → ref wt' , ext}) (≻-preserves wt p r)
≻-preserves (! wt) p (Deref r) = Pr.map id (λ{ (wt' , ext) → ! wt' , ext}) (≻-preserves wt p r)
≻-preserves (y ≔ x) p (Assign₁ r) =
  Pr.map
    id
    (λ{ (y' , ext , q) → y' ≔ ⊒-preserves ext x , ext , q})
    (≻-preserves y p r)
≻-preserves (y ≔ x) p (Assign₂ r) =
  Pr.map
    id
    (λ{ (x' , ext , q) → ⊒-preserves ext y ≔ x' , ext , q})
    (≻-preserves x p r)

-- preservation for multistep reductions
preservation : ∀ {n} {e : Exp n} {Γ Σ A μ μ' e'} →
                Γ , Σ ⊢ e ∶ A →
                Γ , Σ ⊢ μ →
                e , μ ≻* e' , μ' →
                -----------------------------------------------
                ∃ λ Σ' → Γ , Σ' ⊢ e' ∶ A × Σ' ⊒ Σ × Γ , Σ' ⊢ μ'
preservation wt ok ε = _ , wt , ⊑-refl , ok
preservation wt ok (x ◅ r) with ≻-preserves wt ok x
... | Σ₂ , wt' , Σ₂⊒Σ , μ₂ok with preservation wt' μ₂ok r
... | Σ₃ , wt'' , Σ₃⊒Σ₂ , μ₃ = Σ₃ , wt'' , ⊑-trans Σ₂⊒Σ Σ₃⊒Σ₂ , μ₃

{-# NON_TERMINATING #-}
safety : ∀ {e : Exp zero} {Σ A μ} →
         [] , Σ ⊢ e ∶ A →
         [] , Σ ⊢ μ →
         ---------------------------------------
         ∃ λ Σ' → ∃ λ e' → ∃ λ μ' →
            (e , μ ≻* e' , μ') × Val e' × ([] , Σ' ⊢ e' ∶ A)
safety p q with progress q p
safety p q | inj₁ x = _ , _ , _ , ε , x , p
safety p q | inj₂ (e' , μ' , step) with ≻-preserves p q step
... | (Σ₂ , wte' , ext , μ'-ok) with safety wte' μ'-ok
... | (Σ₃ , e'' , μ'' , steps , v , wte'') = Σ₃ , e'' , μ'' , step ◅ steps , v , wte''
