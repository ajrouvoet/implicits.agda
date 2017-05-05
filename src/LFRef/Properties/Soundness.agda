module LFRef.Properties.Soundness where

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

open import LFRef.Syntax
open import LFRef.Welltyped
open import LFRef.Eval

progress : ∀ {𝕊 Σ A} {e : Exp 0} {μ} →
           𝕊 , Σ , [] ⊢ μ →
           𝕊 , Σ , [] ⊢ₑ e ∶ A →
           --------------------------------------
           Val e ⊎ ∃₂ λ e' μ' → (𝕊 ⊢ e , μ ≻ e' , μ')

progress p (tm (con k ts)) = inj₁ tm
progress p (tm unit) = inj₁ tm
progress p (tm (var ()))
progress p (tm (loc x)) = inj₁ tm

progress p (fn ·★ ts) = inj₂ (, (, funapp-β fn (tele-fit-length ts)))

progress p (lett x e) with progress p x
progress p (lett (tm x) e) | inj₁ tm = inj₂ (, (, lett-β))
progress p (lett (_ ·★ _) e) | inj₁ ()
progress p (lett (lett wtx wtx₁) e) | inj₁ ()
progress p (lett (ref wtx) e) | inj₁ ()
progress p (lett (! wtx) e) | inj₁ ()
progress p (lett (wtx ≔ wtx₁) e) | inj₁ ()
progress p (lett x e) | inj₂ (x' , μ' , step) = inj₂ (, (, lett-clos step))

progress p (ref e) with progress p e
progress p (ref {_} {tm x} e) | inj₁ v = inj₂ (, (, ref-val))
progress p (ref {_} {_ ·★ _} e) | inj₁ ()
progress p (ref {_} {lett x x₁} e) | inj₁ ()
progress p (ref {_} {ref x} e) | inj₁ ()
progress p (ref {_} { ! x } e) | inj₁ ()
progress p (ref {_} {x ≔ x₁} e) | inj₁ ()
progress p (ref e) | inj₂ (e' , μ' , step) = inj₂ (, (, ref-clos step))

progress p (!_ {x = x} e) with progress p e
progress p (!_ {_} {tm .(loc _)} (tm (loc x))) | inj₁ tm =
  inj₂ (, (, !-val (P.subst (_<_ _) (pointwise-length p) ([-]=-length x))))
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
  inj₂ (, (, ≔-val (P.subst (_<_ _) (pointwise-length p) ([-]=-length x))))
progress p₁ (tm (loc x₁) ≔ (x ·★ p)) | inj₁ tm | (inj₁ ())
progress p (tm (loc x₁) ≔ lett e e₁) | inj₁ tm | (inj₁ ())
progress p (tm (loc x₁) ≔ ref e) | inj₁ tm | (inj₁ ())
progress p (tm (loc x₁) ≔ (! e)) | inj₁ tm | (inj₁ ())
progress p (tm (loc x₁) ≔ (e ≔ e₁)) | inj₁ tm | (inj₁ ())
progress p (l ≔ e) | inj₂ (_ , _ , step) | _ = inj₂ (, (, ≔-clos₁ step))
progress p (l ≔ e) | _ | (inj₂ (_ , _ , step)) = inj₂ (, (, ≔-clos₂ step))

≻-preserves : ∀ {n Γ 𝕊 Σ A} {e : Exp n} {e' μ' μ} →
              𝕊 , Σ , Γ ⊢ₑ e ∶ A →
              𝕊 , Σ , Γ ⊢ μ →
              𝕊 ⊢ e , μ ≻ e' , μ' →
              -------------------------------------------------------
              ∃ λ Σ' → 𝕊 , Σ' , Γ ⊢ₑ e' ∶ A × Σ' ⊒ Σ × 𝕊 , Σ' , Γ ⊢ μ'
≻-preserves (tm x) q ()
≻-preserves (fn ·★ ts) q p = {!!}
≻-preserves (lett p p₁) q lett-β = {!!}
≻-preserves (lett p p₁) q (lett-clos step) = {!!}
≻-preserves (ref p) q ref-val = {!!}
≻-preserves (ref p) q (ref-clos step) = {!!}
≻-preserves (! p₁) q (!-val p) = {!!}
≻-preserves (! p) q (!-clos step) = {!!}
≻-preserves (p₁ ≔ p₂) q (≔-val p) = {!!}
≻-preserves (p ≔ p₁) q (≔-clos₁ step) = {!!}
≻-preserves (p ≔ p₁) q (≔-clos₂ step) = {!!}
