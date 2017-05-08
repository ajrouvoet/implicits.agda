module LFRef.Properties.Soundness where

open import Data.Nat
open import Data.Sum
open import Data.Product as Pr
open import Data.List
open import Data.Fin using (fromℕ≤; Fin)
open import Data.Vec hiding (_∷ʳ_)
open import Data.Star
open import Function
open import Extensions.List as L

open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.Core using (REL; Reflexive)
open import Relation.Binary.List.Pointwise as PRel hiding (refl)

open import LFRef.Syntax
open import LFRef.Welltyped
open import LFRef.Eval

progress : ∀ {𝕊 Σ A} {e : Exp 0} {μ} →
           𝕊 , Σ , [] ⊢ μ →
           𝕊 , Σ , [] ⊢ₑ e ∶ A →
           --------------------------------------
           ExpVal e ⊎ ∃₂ λ e' μ' → (𝕊 ⊢ e , μ ≻ e' , μ')

progress p (tm (con k ts _)) = inj₁ tm
progress p (tm unit) = inj₁ tm
progress p (tm (var ()))
progress p (tm (loc x)) = inj₁ tm

progress p (_·★_ fn ts q) = inj₂ (, (, funapp-β fn (tele-fit-length ts)))

progress p (lett x e) with progress p x
progress p (lett (tm x) e) | inj₁ tm = inj₂ (, (, lett-β))
progress p (lett (_·★_ _ _ _) e) | inj₁ ()
progress p (lett (lett wtx wtx₁) e) | inj₁ ()
progress p (lett (ref wtx) e) | inj₁ ()
progress p (lett (! wtx) e) | inj₁ ()
progress p (lett (wtx ≔ wtx₁) e) | inj₁ ()
progress p (lett x e) | inj₂ (x' , μ' , step) = inj₂ (, (, lett-clos step))

progress p (ref e) with progress p e
progress p (ref {_} {tm x} e) | inj₁ v = inj₂ (, (, ref-val {!!}))
progress p (ref {_} {_ ·★ _} e) | inj₁ ()
progress p (ref {_} {lett x x₁} e) | inj₁ ()
progress p (ref {_} {ref x} e) | inj₁ ()
progress p (ref {_} { ! x } e) | inj₁ ()
progress p (ref {_} {x ≔ x₁} e) | inj₁ ()
progress p (ref e) | inj₂ (e' , μ' , step) = inj₂ (, (, ref-clos step))

progress p (!_ {x = x} e) with progress p e
progress p (!_ {_} {tm .(loc _)} (tm (loc x))) | inj₁ tm =
  inj₂ (, (, !-val (P.subst (_<_ _) (pointwise-length p) ([]=-length x))))
progress p (!_ {_} {tm (var ())} e) | _
progress p (!_ {_} {_ ·★ _} e) | inj₁ ()
progress p (!_ {_} {lett x x₁} e) | inj₁ ()
progress p (!_ {_} {ref x} e) | inj₁ ()
progress p (!_ {_} { ! x } e) | inj₁ ()
progress p (!_ {_} {x ≔ x₁} e) | inj₁ ()
progress p (! e) | inj₂ (e' , μ' , step) = inj₂ (, (, !-clos step))

progress p (l ≔ e) with progress p l | progress p e
progress p (tm (var ()) ≔ _) | inj₁ tm | (inj₁ _)
progress p (tm (loc x) ≔ tm _) | inj₁ tm | (inj₁ _) =
  inj₂ (, (, ≔-val (P.subst (_<_ _) (pointwise-length p) ([]=-length x)) {!!}))
progress p₁ (tm (loc x₁) ≔ (_·★_ x p q)) | inj₁ tm | (inj₁ ())
progress p (tm (loc x₁) ≔ lett e e₁) | inj₁ tm | (inj₁ ())
progress p (tm (loc x₁) ≔ ref e) | inj₁ tm | (inj₁ ())
progress p (tm (loc x₁) ≔ (! e)) | inj₁ tm | (inj₁ ())
progress p (tm (loc x₁) ≔ (e ≔ e₁)) | inj₁ tm | (inj₁ ())
progress p (l ≔ e) | inj₂ (_ , _ , step) | _ = inj₂ (, (, ≔-clos₁ step))
progress p (l ≔ e) | _ | (inj₂ (_ , _ , step)) = inj₂ (, (, ≔-clos₂ step))

postulate

  lem₂ : ∀ {n 𝕊 Σ e a b t} {Γ : Ctx n} →
           𝕊 , weaken₁-Σ Σ , (a :+: Γ) ⊢ₑ e ∶ weaken₁-tp b →
           𝕊 , Σ , Γ ⊢ t ∶ a →
           𝕊 , Σ , Γ ⊢ₑ (e exp/ (sub t)) ∶ b

lem₁ : ∀ {n 𝕊 Σ φ ts} {Γ : Ctx n} →
        𝕊 ⊢ φ fnOk →
        (p : 𝕊 , Σ , Γ ⊢ ts ∶ⁿ weaken+-tele n (Fun.args φ)) →
        (q : length ts ≡ (Fun.m φ)) →
        𝕊 , Σ , Γ ⊢ₑ (!call (Fun.body φ) ts q) ∶ ((Fun.returntype φ) fun[ ts / q ])
lem₁ ok p q = {!!}

!load-ok : ∀ {n Σ Σ' A μ i 𝕊} {Γ : Ctx n} →
            Rel (λ A x → 𝕊 , Σ , Γ ⊢ (proj₁ x) ∶ A) Σ' μ →
            Σ' L.[ i ]= A → (l : i < length μ) → 𝕊 , Σ , Γ ⊢ (!load μ l) ∶ A
!load-ok [] ()
!load-ok (x∼y ∷ p) here (s≤s z≤n) = x∼y
!load-ok (x∼y ∷ p) (there q) (s≤s l) = !load-ok p q l

⊒-preserves-tele : ∀ {n m Γ Σ Σ' 𝕊} {ts : List (Term n)} {T : Tele n m}→ Σ' ⊒ Σ →
                   𝕊 , Σ , Γ ⊢ ts ∶ⁿ T →
                   𝕊 , Σ' , Γ ⊢ ts ∶ⁿ T
⊒-preserves-tele ext p = {!!}

⊒-preserves-tm : ∀ {n Γ Σ Σ' A 𝕊} {t : Term n} → Σ' ⊒ Σ → 𝕊 , Σ , Γ ⊢ t ∶ A → 𝕊 , Σ' , Γ ⊢ t ∶ A
⊒-preserves-tm ext unit = unit
⊒-preserves-tm ext (var x) = var x
⊒-preserves-tm ext (con x p q) = con x (⊒-preserves-tele ext p) q
⊒-preserves-tm ext (loc x) = loc (xs⊒ys[i] x ext)

⊒-preserves : ∀ {n Γ Σ Σ' A 𝕊} {e : Exp n} → Σ' ⊒ Σ → 𝕊 , Σ , Γ ⊢ₑ e ∶ A → 𝕊 , Σ' , Γ ⊢ₑ e ∶ A
⊒-preserves ext (tm x) = tm (⊒-preserves-tm ext x)
⊒-preserves ext ((x ·★ p) q) = {!!}
⊒-preserves ext (lett p p₁) = {!!}
⊒-preserves ext (ref p) = {!!}
⊒-preserves ext (! p) = {!!}
⊒-preserves ext (p ≔ p₁) = {!!}

≻-preserves : ∀ {n Γ 𝕊 Σ A} {e : Exp n} {e' μ' μ} →
              𝕊 , Γ ⊢ok →
              𝕊 , Σ , Γ ⊢ₑ e ∶ A →
              𝕊 , Σ , Γ ⊢ μ →
              𝕊 ⊢ e , μ ≻ e' , μ' →
              -------------------------------------------------------
              ∃ λ Σ' → 𝕊 , Σ' , Γ ⊢ₑ e' ∶ A × Σ' ⊒ Σ × 𝕊 , Σ' , Γ ⊢ μ'
≻-preserves ok (tm x) q ()

≻-preserves {Σ = Σ} ok (_·★_ fn ts refl) q (funapp-β x refl) with
  []=-functional _ _  fn x | all-lookup fn (_,_⊢ok.funs-ok ok)
... | refl | z = Σ , (lem₁ (all-lookup fn (_,_⊢ok.funs-ok ok)) ts refl) , ⊑-refl , q

≻-preserves {Σ = Σ} ok (lett (tm x) p) q lett-β = Σ , lem₂ p x , ⊑-refl , q
≻-preserves ok (lett p p₁) q (lett-clos step) with ≻-preserves ok p q step
≻-preserves ok (lett p p₁) q (lett-clos step) | Σ₂ , wte' , Σ₂⊒Σ₁ , q' =
  Σ₂ , (lett wte' (⊒-preserves (⊑-map Σ₂⊒Σ₁) p₁) , Σ₂⊒Σ₁ , q')

≻-preserves {Σ = Σ} ok (ref {A = A} (tm x)) q (ref-val v) = let ext = (∷ʳ-⊒ A Σ) in
  Σ ∷ʳ A ,
  (tm (loc (P.subst (λ i → _ L.[ i ]= _) (pointwise-length q) (∷ʳ[length] Σ)))) ,
  ext , pointwise-∷ʳ (PRel.map (⊒-preserves-tm ext) q) (⊒-preserves-tm ext x)

≻-preserves ok (ref p) q (ref-clos step) = {!!}

≻-preserves {Σ = Σ₁} ok (! tm (loc x)) q (!-val p) = Σ₁ , tm (!load-ok q x p) , ⊑-refl , q
≻-preserves ok (! p) q (!-clos step) = {!!}

≻-preserves {σ = σ₁} ok (_≔_ {a = a} (tm (loc x)) (tm y)) q (≔-val p v) =
  σ₁ , tm unit , ⊑-refl , pointwise-[]≔ q x p y
≻-preserves ok (p ≔ p₁) q (≔-clos₁ step) = {!!}
≻-preserves ok (p ≔ p₁) q (≔-clos₂ step) = {!!}
