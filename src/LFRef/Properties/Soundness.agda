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
           Val e ⊎ ∃₂ λ e' μ' → (e , μ ≻ e' , μ')

progress p (tm unit) = inj₁ unit
progress p (tm (var ()))
progress p (tm (loc x)) = inj₁ (loc _)

progress p (lett x e) with progress p x
progress p (lett {_} {tm x} wtx e) | inj₁ _ = inj₂ (, (, lett-β))
progress p (lett {_} {ƛ _ _} wtx e) | inj₁ ()
progress p (lett {_} {_ · _} wtx e) | inj₁ ()
progress p (lett {_} {lett x x₁} wtx e) | inj₁ ()
progress p (lett {_} {ref x} wtx e) | inj₁ ()
progress p (lett {_} { ! x } wtx e) | inj₁ ()
progress p (lett {_} {x ≔ x₁} wtx e) | inj₁ ()
progress p (lett x e) | inj₂ (x' , μ' , step) = inj₂ (, (, lett-clos₁ step))

progress p (ref e) with progress p e
progress p (ref {_} {tm x} e) | inj₁ v = inj₂ (, (, ref-val))
progress p (ref {_} {ƛ _ _} e) | inj₁ ()
progress p (ref {_} {_ · _} e) | inj₁ ()
progress p (ref {_} {lett x x₁} e) | inj₁ ()
progress p (ref {_} {ref x} e) | inj₁ ()
progress p (ref {_} { ! x } e) | inj₁ ()
progress p (ref {_} {x ≔ x₁} e) | inj₁ ()
progress p (ref e) | inj₂ (e' , μ' , step) = inj₂ (, (, ref-clos step))

progress p (!_ {x = x} e) with progress p e
progress p (!_ {_} {tm .(loc _)} (tm (loc x))) | inj₁ (loc i) =
  inj₂ (, (, !-val (P.subst (_<_ _) (pointwise-length p) ([-]=-length x))))
progress p (!_ {_} {tm (var _)} e) | inj₁ ()
progress p (!_ {_} {ƛ _ _} e) | inj₁ ()
progress p (!_ {_} {_ · _} e) | inj₁ ()
progress p (!_ {_} {lett x x₁} e) | inj₁ ()
progress p (!_ {_} {ref x} e) | inj₁ ()
progress p (!_ {_} { ! x } e) | inj₁ ()
progress p (!_ {_} {x ≔ x₁} e) | inj₁ ()
progress p (! e) | inj₂ y = {!!}

progress p (ƛ x₁ x₂) = {!!}
progress p (x · x₁) = {!!}
progress p (x₁ ≔ x₂) = {!!}
