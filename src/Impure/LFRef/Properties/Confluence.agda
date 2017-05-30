module Impure.LFRef.Properties.Confluence where

open import Prelude
open import Data.List
open import Extensions.List
open import Extensions.Nat

open import Impure.LFRef.Syntax
open import Impure.LFRef.Eval

private
  val-lemma : ∀ {t} → (v v₁ : Val t)  → v ≡ v₁
  val-lemma loc loc = refl
  val-lemma unit unit = refl
  val-lemma con con = refl

-- A stronger property than Church-Rosser
deterministic : ∀ {𝕊 e e' e'' μ μ' μ''} →
                𝕊 ⊢ e , μ ≻ e' , μ' → 𝕊 ⊢ e , μ ≻ e'' , μ'' →
                ---------------------------------------------
                e' ≡ e'' × μ' ≡ μ''
deterministic (funapp-β x p₁) (funapp-β x' p) with []=-functional _ _ x x'
deterministic (funapp-β x refl) (funapp-β x' refl) | refl = refl , refl
deterministic {μ = μ} (ref-val p) (ref-val q) = refl , cong (λ v → μ ∷ʳ (, v)) (val-lemma p q)
deterministic (ref-val v) (ref-clos ())
deterministic (≔-val p v) (≔-val q w) with <-unique p q | val-lemma v w
... | refl | refl = refl , refl
deterministic (≔-val p v) (≔-clos₁ ())
deterministic (≔-val p v) (≔-clos₂ _ ())
deterministic {μ = μ} (!-val p) (!-val q) = (cong (λ v → tm (!load μ v)) (<-unique p q)) , refl
deterministic (!-val p) (!-clos ())
deterministic (ref-clos ()) (ref-val v)
deterministic (ref-clos p) (ref-clos q) with deterministic p q
... | refl , refl = refl , refl
deterministic (!-clos ()) (!-val p)
deterministic (!-clos p) (!-clos q) with deterministic p q
... | refl , refl = refl , refl
deterministic (≔-clos₁ ()) (≔-val p v)
deterministic (≔-clos₁ p) (≔-clos₁ q) with deterministic p q
... | refl , refl = refl , refl
deterministic (≔-clos₁ ()) (≔-clos₂ (tm x) q)
deterministic (≔-clos₂ (tm x) p) (≔-clos₁ ())
deterministic (≔-clos₂ _ ()) (≔-val p v)
deterministic (≔-clos₂ _ p) (≔-clos₂ _ q) with deterministic p q
... | refl , refl = refl , refl

deterministic-seq : ∀ {𝕊 e e' e'' μ μ' μ''} →
                𝕊 ⊢ e , μ ≻ₛ e' , μ' →
                𝕊 ⊢ e , μ ≻ₛ e'' , μ'' →
                ---------------------------------------------
                e' ≡ e'' × μ' ≡ μ''
deterministic-seq lett-β lett-β = refl , refl
deterministic-seq lett-β (lett-clos ())
deterministic-seq (lett-clos ()) lett-β
deterministic-seq (lett-clos p) (lett-clos q) with deterministic p q
... | refl , refl = refl , refl
deterministic-seq (ret-clos x) (ret-clos x') with deterministic x x'
... | refl , refl = refl , refl

open import Data.Star
confluence : ∀ {𝕊 e e' e'' μ μ' μ''} →
             𝕊 ⊢ e , μ ≻⋆ e' , μ' → 𝕊 ⊢ e , μ ≻⋆ e'' , μ'' →
             SeqExpVal e' → SeqExpVal e'' →
             -----------------------------------------------
             e' ≡ e'' × μ' ≡ μ''
confluence ε ε z y = refl , refl
confluence ε (ret-clos () ◅ _) (ret-tm _) _
confluence (ret-clos () ◅ _) ε _ (ret-tm _)
confluence (lett-β ◅ _) ε _ ()
confluence (lett-clos _ ◅ _) ε _ ()
confluence (x ◅ p) (x' ◅ p') v w with deterministic-seq x x'
... | refl , refl with confluence p p' v w
... | refl , refl = refl , refl
