module LFRef.Properties.Soundness where

open import Data.Nat
open import Data.Sum
open import Data.Product as Pr
open import Data.List as List
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
open import LFRef.Properties.Decidable

progress : ∀ {𝕊 Σ A} {e : Exp 0} {μ} →
           𝕊 , Σ ⊢ μ →
           𝕊 , Σ , [] ⊢ₑ e ∶ A →
           --------------------------------------
           (ExpVal e) ⊎ (∃₂ λ e' μ' → (𝕊 ⊢ e , μ ≻ e' , μ'))

progress p (tm (con k ts _)) = inj₁ (tm con)
progress p (tm unit) = inj₁ (tm unit)
progress p (tm (var ()))
progress p (tm (loc x)) = inj₁ (tm loc)

progress p (fn ·★[ q ] ts) = inj₂ (, (, funapp-β fn (tele-fit-length ts)))

progress p (ref e) with progress p e
progress p (ref {_} {tm _} (tm _)) | inj₁ (tm v) = inj₂ (, (, ref-val v))
progress p (ref {_} {_ ·★ _} e) | inj₁ ()
progress p (ref {_} {ref x} e) | inj₁ ()
progress p (ref {_} { ! x } e) | inj₁ ()
progress p (ref {_} {x ≔ x₁} e) | inj₁ ()
progress p (ref e) | inj₂ (e' , μ' , step) = inj₂ (, (, ref-clos step))

progress p (!_ {x = x} e) with progress p e
progress p (!_ {_} {tm .(loc _)} (tm (loc x))) | inj₁ (tm _) =
  inj₂ (, (, !-val (P.subst (_<_ _) (pointwise-length p) ([]=-length x))))
progress p (!_ {_} {tm (var ())} e) | _
progress p (!_ {_} {_ ·★ _} e) | inj₁ ()
progress p (!_ {_} {ref x} e) | inj₁ ()
progress p (!_ {_} { ! x } e) | inj₁ ()
progress p (!_ {_} {x ≔ x₁} e) | inj₁ ()
progress p (! e) | inj₂ (e' , μ' , step) = inj₂ (, (, !-clos step))

progress p (l ≔ e) with progress p l | progress p e
progress p (tm () ≔ e) | inj₁ (tm unit) | (inj₁ (tm x₁))
progress p (tm () ≔ e) | inj₁ (tm con) | (inj₁ (tm x₁))
progress p (tm (loc x) ≔ e) | inj₁ (tm loc) | (inj₁ (tm v)) =
  inj₂ (, (, ≔-val (P.subst (_<_ _) (pointwise-length p) ([]=-length x)) v))
progress p (l ≔ e) | inj₂ (_ , _ , step) | _ = inj₂ (, (, ≔-clos₁ step))
progress p (l ≔ e) | inj₁ v | (inj₂ (_ , _ , step)) = inj₂ (, (, ≔-clos₂ v step))

{-}
progress p (lett x e) with progress p x
progress p (lett (tm x) e) | inj₁ (tm _) = inj₂ (, (, lett-β))
progress p (lett (_·★_ _ _ _) e) | inj₁ ()
progress p (lett (lett wtx wtx₁) e) | inj₁ ()
progress p (lett (ref wtx) e) | inj₁ ()
progress p (lett (! wtx) e) | inj₁ ()
progress p (lett (wtx ≔ wtx₁) e) | inj₁ ()

progress p (lett x e) | inj₂ (x' , μ' , step) = inj₂ (, (, lett-clos step))
-}

postulate

  lem₂ : ∀ {n 𝕊 Σ e a b t} {Γ : Ctx n} →
           𝕊 , Σ , (a :+: Γ) ⊢ₑ e ∶ weaken₁-tp b →
           𝕊 , Σ , Γ ⊢ t ∶ a →
           𝕊 , Σ , Γ ⊢ₑ (e exp/ (sub t)) ∶ b

  lem₁ : ∀ {n 𝕊 Σ φ ts} {Γ : Ctx n} →
          𝕊 ⊢ φ fnOk →
          (p : 𝕊 , Σ , Γ ⊢ ts ∶ⁿ weaken+-tele n (Fun.args φ)) →
          (q : length ts ≡ (Fun.m φ)) →
          𝕊 , Σ , Γ ⊢ₑ (!call (Fun.body φ) ts q) ∶ ((Fun.returntype φ) fun[ ts / q ])

-- loading from a welltyped store results in a welltyped term
!load-ok : ∀ {Σ Σ' A μ i 𝕊} →
            -- store-welltypedness type (strengthened for induction)
            Rel (λ A x → 𝕊 , Σ , [] ⊢ (proj₁ x) ∶ A) Σ' μ →
            Σ' L.[ i ]= A → (l : i < length μ) →
            𝕊 , Σ , [] ⊢ (!load μ l) ∶ A
!load-ok [] ()
!load-ok (x∼y ∷ p) here (s≤s z≤n) = x∼y
!load-ok (x∼y ∷ p) (there q) (s≤s l) = !load-ok p q l

mutual
  ⊒-preserves-tm : ∀ {n Γ Σ Σ' A 𝕊} {t : Term n} → Σ' ⊒ Σ → 𝕊 , Σ , Γ ⊢ t ∶ A → 𝕊 , Σ' , Γ ⊢ t ∶ A
  ⊒-preserves-tm ext unit = unit
  ⊒-preserves-tm ext (var x) = var x
  ⊒-preserves-tm ext (con x p q) = con x (⊒-preserves-tele ext p) q
  ⊒-preserves-tm ext (loc x) = loc (xs⊒ys[i] x ext)

  ⊒-preserves-tele : ∀ {n m Γ Σ Σ' 𝕊} {ts : List (Term n)} {T : Tele n m} → Σ' ⊒ Σ →
                    𝕊 , Σ , Γ ⊢ ts ∶ⁿ T →
                    𝕊 , Σ' , Γ ⊢ ts ∶ⁿ T
  ⊒-preserves-tele ext ε = ε
  ⊒-preserves-tele ext (x ⟶ p) = ⊒-preserves-tm ext x ⟶ (⊒-preserves-tele ext p)

-- welltypedness is preseved under store extensions
⊒-preserves : ∀ {n Γ Σ Σ' A 𝕊} {e : Exp n} → Σ' ⊒ Σ → 𝕊 , Σ , Γ ⊢ₑ e ∶ A → 𝕊 , Σ' , Γ ⊢ₑ e ∶ A
⊒-preserves ext (tm x) = tm (⊒-preserves-tm ext x)
⊒-preserves ext (x ·★[ refl ] p) with ⊒-preserves-tele ext p
... | p' = x ·★[ refl ] p'

⊒-preserves ext (ref p) = ref (⊒-preserves ext p)
⊒-preserves ext (! p) = ! (⊒-preserves ext p)
⊒-preserves ext (p ≔ q) = ⊒-preserves ext p ≔ ⊒-preserves ext q

-- helper for lifting preserving reductions into their closure
clos-cong : ∀ {Σ μ 𝕊 A B} {e : Exp 0} (c : Exp 0 → Exp 0) →
                (f : ∀ {Σ'} (ext : Σ' ⊒ Σ) → 𝕊 , Σ' , [] ⊢ₑ e ∶ A → 𝕊 , Σ' , [] ⊢ₑ c e ∶ B) →
                (∃ λ Σ' → 𝕊 , Σ' , [] ⊢ₑ e ∶ A × Σ' ⊒ Σ × 𝕊 , Σ' ⊢ μ) →
                ∃ λ Σ' → 𝕊 , Σ' , [] ⊢ₑ c e ∶ B × Σ' ⊒ Σ × 𝕊 , Σ' ⊢ μ
clos-cong _ f (Σ , wte , ext , μ-wt) = Σ , f ext wte , ext , μ-wt

≻-preserves : ∀ {𝕊 Σ A} {e : Exp 0} {e' μ' μ} →
              𝕊 , [] ⊢ok →
              𝕊 , Σ , [] ⊢ₑ e ∶ A →
              𝕊 , Σ ⊢ μ →
              𝕊 ⊢ e , μ ≻ e' , μ' →
              ----------------------------------------------------
              ∃ λ Σ' → 𝕊 , Σ' , [] ⊢ₑ e' ∶ A × Σ' ⊒ Σ × 𝕊 , Σ' ⊢ μ'

-- variables
≻-preserves ok (tm x) q ()

-- function application
≻-preserves {Σ = Σ} ok (fn ·★[ refl ] ts) q (funapp-β x refl) with
  []=-functional _ _  fn x | all-lookup fn (_,_⊢ok.funs-ok ok)
... | refl | fn-ok = Σ , (lem₁ fn-ok ts refl) , ⊑-refl , q

-- new references
≻-preserves {Σ = Σ} ok (ref {A = A} (tm x)) q (ref-val v) = let ext = (∷ʳ-⊒ A Σ) in
  Σ ∷ʳ A ,
  (tm (loc (P.subst (λ i → _ L.[ i ]= _) (pointwise-length q) (∷ʳ[length] Σ A)))) ,
  ext ,
  pointwise-∷ʳ (PRel.map (⊒-preserves-tm ext) q) (⊒-preserves-tm ext x)
≻-preserves ok (ref p) q (ref-clos step) =
  clos-cong
    ref (const ref)
    (≻-preserves ok p q step)

-- dereferencing
≻-preserves {Σ = Σ₁} ok (! tm (loc x)) q (!-val p)
  = Σ₁ , tm (!load-ok q x p) , ⊑-refl , q
≻-preserves ok (! p) q (!-clos step) =
  clos-cong
    !_ (const !_)
    (≻-preserves ok p q step)

-- assignment
≻-preserves {Σ = Σ₁} ok (_≔_ (tm (loc x)) (tm y)) q (≔-val p v) =
  Σ₁ , tm unit , ⊑-refl , pointwise-[]≔ q x p y
≻-preserves ok (p ≔ p₁) q (≔-clos₁ step) =
  clos-cong
    (λ p' → p' ≔ _) (λ ext p' → p' ≔ ⊒-preserves ext p₁)
    (≻-preserves ok p q step)
≻-preserves ok (p ≔ p₁) q (≔-clos₂ v step) =
  clos-cong
    (λ p' → _ ≔ p') (λ ext p' → ⊒-preserves ext p ≔ p')
    (≻-preserves ok p₁ q step)

{-}

-- let binding
≻-preserves {Σ = Σ} ok (lett (tm x) p) q lett-β = Σ , lem₂ p x , ⊑-refl , q
≻-preserves ok (lett p p₁) q (lett-clos step) with ≻-preserves ok p q step
... | Σ₂ , wte' , Σ₂⊒Σ₁ , q' =
  Σ₂ , lett wte' ((⊒-preserves Σ₂⊒Σ₁ p₁)) , Σ₂⊒Σ₁ , q'
-}
