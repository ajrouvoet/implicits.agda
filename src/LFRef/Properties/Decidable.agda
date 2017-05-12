module LFRef.Properties.Decidable where

open import Prelude hiding (sym)
open import Relation.Unary
open import Relation.Nullary.Decidable as DecM
open import Data.List
open import Data.Vec
open import Data.Vec.Properties
open import Function.Inverse
open import Function.Equality
open import Extensions.List as List↑ using ()
open import Extensions.Vec as Vec↑ using ()

open import LFRef.Syntax
open import LFRef.Welltyped

-- decidable type equality
_ty≟_ : ∀ {n} (a b : Type n) → Dec (a ≡ b)
a ty≟ b = {!!}

unique-tm-type : ∀ {n a b} 𝕊 Σ Γ (t : Term n) → 𝕊 , Σ , Γ ⊢ t ∶ a → 𝕊 , Σ , Γ ⊢ t ∶ b → a ≡ b
unique-tm-type 𝕊 Σ Γ .unit unit unit = refl
unique-tm-type 𝕊 Σ Γ .(var _) (var x) (var x') with Vec↑.[]=-functional Γ _ x x'
... | refl = refl
unique-tm-type 𝕊 Σ Γ .(loc _) (loc x) (loc x') with List↑.[]=-functional Σ _ x x'
... | refl = refl
unique-tm-type 𝕊 Σ Γ .(con _ _) (con x p q₁) (con x₁ p₁ q) = {!!}

mutual
  type-tm : ∀ {n} 𝕊 Σ Γ (t : Term n) → Dec (∃ λ a → 𝕊 , Σ , Γ ⊢ t ∶ a)
  type-tm 𝕊 Σ Γ (var x) =
    yes (, var (proj₂ (Vec↑.strong-lookup _ _)))
  type-tm 𝕊 Σ Γ (loc x) =
    DecM.map′
      (λ{ (_ , p)  → Ref _ , loc p})
      (λ{ (_ , loc p) → _ , p })
      (List↑.dec-lookup x Σ)
  type-tm 𝕊 Σ Γ unit = yes (Unit , unit)
  type-tm 𝕊 Σ Γ (con c ts) with (List↑.dec-lookup c (Sig.constructors 𝕊))
  ... | no ¬p = no (λ{ (._ , con p _ _) → ¬p (, p)})
  ... | yes p with type-tele 𝕊 Σ Γ ts (weaken+-tele _ (ConType.args (proj₁ p)))
  ... | no ¬q = no (λ{ (._ , con p' q _) → ¬q {!q!} })
  ... | yes q = {!!}

  type-tele : ∀ {n m } 𝕊 Σ Γ (ts : List (Term n)) → (T : Tele n m) → Dec (𝕊 , Σ , Γ ⊢ ts ∶ⁿ T)
  type-tele ts T = {!!}

type : ∀ {n} 𝕊 Σ Γ (e : Exp n) → Dec (∃ λ a → 𝕊 , Σ , Γ ⊢ₑ e ∶ a)
type 𝕊 Σ Γ (tm t) = DecM.map′
  (λ x → _ , (tm (proj₂ x)))
  (λ{ (_ , tm x) → , x})
  (type-tm 𝕊 Σ Γ t)
type 𝕊 Σ Γ (fn ·★ as) = {!!}
type 𝕊 Σ Γ (lett e e₁) = {!!}
type 𝕊 Σ Γ (ref e) = {!!}
type 𝕊 Σ Γ (! e) = {!!}
type 𝕊 Σ Γ (e ≔ e₁) = {!!}
